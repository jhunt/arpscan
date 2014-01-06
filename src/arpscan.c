/*
  Copyright 2014 James Hunt <james@jameshunt.us>

  This file is part of arpscan.

  arpscan is free software: you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation, either version 3 of the License, or
  (at your option) any later version.

  arpscan is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with arpscan.  If not, see <http://www.gnu.org/licenses/>.
 */

#define VERSION "1.0.0"

#include <stdio.h>
#include <string.h>
#include <strings.h>
#include <stdint.h>
#include <stdlib.h>
#include <errno.h>

#include <unistd.h>
#include <fcntl.h>

#include <sys/types.h>
#include <sys/socket.h>
#include <sys/ioctl.h>
#include <sys/time.h>

#include <arpa/inet.h>

#include <net/if.h>
#include <net/if_arp.h>
#include <linux/if_packet.h>

#include <netinet/ip.h>
#include <netinet/ether.h>

#include <getopt.h>

/***************************************************************/

#define DUMP_COLS 16
#define ETHER_MAC_FMT "%02x:%02x:%02x:%02x:%02x:%02x"
#define IPv4_ADDR_FMT "%u.%u.%u.%u"

#define ARP_HDRLEN 28
#define ONE_SEC 1 * 1000 * 1000

/***************************************************************/

typedef void ip_callback(struct in_addr*);

/***************************************************************/

static struct {
	char     *device;  /* name of interface to scan from */
	char     *network; /* network (CIDR) to scan */
	uint32_t  timeout; /* ms to wait for a new ARP reply */
	uint8_t   debug;   /* how chatty should we be? */
} OPTIONS = {
	NULL, /* no device */
	NULL, /* no network */
	500,  /* 500ms timeout */
	0,    /* no debug output */
};

#define WANT_INFO  (OPTIONS.debug >= 1)
#define WANT_DEBUG (OPTIONS.debug >= 2)
#define WANT_TRACE (OPTIONS.debug >= 4)

#define DEBUG_RC(sys,fn,rc) if (WANT_DEBUG) { fprintf(stderr, sys ": call to " fn " returned %i\n", (int)(rc)); }

static struct ether_arp ARP = {
	.arp_hrd = ARPHRD_ETHER,
	.arp_pro = ETHERTYPE_IP,
	.arp_hln = ETHER_ADDR_LEN,
	.arp_pln = 4, /* IPv4 addr octet-length */
	.arp_op  = ARPOP_REQUEST,
};
static struct sockaddr_ll LL = {0};
static int SOCK;

/***************************************************************/

static void dump(const uint8_t*, ssize_t);

static uint32_t bitmask(uint8_t);
static void for_each_ip(const char *, ip_callback);

static int arp_from(const char*, struct ether_arp*, struct sockaddr_ll*);
static uint8_t* arp_pack(const struct ether_arp*, uint8_t*);
static struct ether_arp* arp_unpack(uint8_t*, struct ether_arp*);

static void send_arp_request(struct in_addr*);
static void recv_arp_replies(uint32_t timeout);

/***************************************************************/

static void
dump(const uint8_t *data, ssize_t len)
{
	ssize_t i;

	if (!WANT_TRACE) return;
	for (i = 0; i < len;) {
		fprintf(stderr, " %02x", data[i]);
		if (++i % DUMP_COLS == 0) fprintf(stderr, "\n");
	}
	if (len % DUMP_COLS != 0) fprintf(stderr, "\n");
	fprintf(stderr, "\n");
}

static uint32_t
bitmask(uint8_t bits)
{
	uint32_t m = 0;
	if (WANT_DEBUG) fprintf(stderr, "calculating bitmask for /%i\n", bits);

	while (bits--) m = (m << 1) + 1;

	if (WANT_DEBUG) fprintf(stderr, "dotted-quad netmask is %s\n",
		inet_ntoa(*(struct in_addr*)(&m)));
	return m;
}

static void
for_each_ip(const char *network, ip_callback cb)
{
	char host_part[INET_ADDRSTRLEN], net_part[3];
	uint32_t first, last, mask;
	char *off;
	struct in_addr ipv4;

	off = index(network, '/');
	if (!off || off - network > sizeof(host_part) - 1 || strlen(off) > 3) {
		fprintf(stderr, "%s doesn't look like CIDR notation\n", network);
		return;
	}

	memcpy(host_part, network, off - network);
	host_part[off - network] = '\0';

	/* extract the network CIDR mask */
	strncpy(net_part, ++off, 2);
	net_part[strlen(off)] = '\0';

	/* calculate the netmask based on net_part */
	mask = atoi(net_part); /* FIXME: use strto*, to detect errors */

	if (inet_pton(AF_INET, host_part, &ipv4) != 1) {
		fprintf(stderr, "failed to parse %s as an IP address\n", host_part);
		return;
	}

	first = (ntohl(ipv4.s_addr) & ntohl(bitmask(mask))) - 1;
	last  = first + (1 << (32 - mask));
	while (++first <= last) {
		ipv4.s_addr = htonl(first);
		(*cb)(&ipv4);
	}
}

static int
arp_from(const char *dev, struct ether_arp *arp, struct sockaddr_ll *ll)
{
	int sockfd, rc;
	struct ifreq iface;
	struct sockaddr_in *sa;

	if (WANT_DEBUG) fprintf(stderr, "arp_from: getting a raw/IP socket\n");
	sockfd = socket(AF_INET, SOCK_RAW, IPPROTO_RAW);
	if (sockfd < 0) {
		DEBUG_RC("arp_form", "socket()", sockfd);
		perror("failed to aquire a raw IP socket");
		return 1;
	}

	strncpy(iface.ifr_name, dev, IFNAMSIZ);
	iface.ifr_name[IFNAMSIZ-1] = '\0';

	if (WANT_DEBUG) fprintf(stderr, "arp_from: issuing ioctl query for '%s' interface HW addr\n", iface.ifr_name);
	if ((rc = ioctl(sockfd, SIOCGIFHWADDR, &iface)) < 0) {
		DEBUG_RC("arp_from", "ioctl()", rc);
		perror("failed to retrieve HW address for device");
		close(sockfd);
		return 1;
	}

	if (WANT_DEBUG) fprintf(stderr, "arp_from: set ARP source HW addres to " ETHER_MAC_FMT "\n",
			iface.ifr_hwaddr.sa_data[0], iface.ifr_hwaddr.sa_data[1], iface.ifr_hwaddr.sa_data[2],
			iface.ifr_hwaddr.sa_data[3], iface.ifr_hwaddr.sa_data[4], iface.ifr_hwaddr.sa_data[5]);

	if (!memcpy(arp->arp_sha, iface.ifr_hwaddr.sa_data, 6)) {
		if (WANT_DEBUG) fprintf(stderr, "arp_from: call to memcpy() failed");
		perror("failed to set ARP source HW address");
		close(sockfd);
		return 1;
	}

	if (ll) {
		ll->sll_ifindex = if_nametoindex(dev);
		if (WANT_DEBUG) fprintf(stderr, "Set LL sockaddr interface index to %i\n", ll->sll_ifindex);
	} else {
		if (WANT_DEBUG) fprintf(stderr, "No LL sockaddr given; skipping index\n");
	}

	if (WANT_DEBUG) fprintf(stderr, "arp_from: issuing ioctl query for '%s' protocol addr\n", iface.ifr_name);
	if ((rc = ioctl(sockfd, SIOCGIFADDR, &iface)) < 0) {
		DEBUG_RC("arp_from", "ioctl()", rc);
		perror("failed to retrieve IP address for device");
		close(sockfd);
		return 1;
	}

	sa = ((struct sockaddr_in*)(&iface.ifr_addr));
	if (!memcpy(arp->arp_spa, &sa->sin_addr, 4)) {
		perror("arp_from:memcpy(arp_spa)");
		close(sockfd);
	}

	close(sockfd);
	return 0;
}

static uint8_t*
arp_pack(const struct ether_arp *arp, uint8_t *data)
{
	if (WANT_DEBUG) fprintf(stderr, "arp_pack: packing ARP header\n");
	if (!data) {
		if (WANT_DEBUG) fprintf(stderr, "arp_ack: no data buffer specified; allocating one\n");
		data = calloc(ARP_HDRLEN, sizeof(uint8_t));
		if (!data) {
			perror("failed to allocate a data buffer for packing the ARP header");
			return NULL;
		}
	}

#define byte(x) (x & 0xff)
#define hi16(x) byte(x)
#define lo16(x) byte(x >> 8)

	data[0] = lo16(arp->arp_hrd);
	data[1] = hi16(arp->arp_hrd);

	data[2] = lo16(arp->arp_pro);
	data[3] = hi16(arp->arp_pro);

	data[4] = byte(arp->arp_hln);
	data[5] = byte(arp->arp_pln);

	data[6] = lo16(arp->arp_op);
	data[7] = hi16(arp->arp_op);

	memcpy(data +  8, arp->arp_sha, 6);
	memcpy(data + 14, arp->arp_spa, 4);
	memcpy(data + 18, arp->arp_tha, 6);
	memcpy(data + 24, arp->arp_tpa, 4);

#undef byte
#undef lo16
#undef hi16

	return data;
}

static struct ether_arp*
arp_unpack(uint8_t *data, struct ether_arp *arp)
{
	uint16_t u16;

	if (WANT_DEBUG) fprintf(stderr, "arp_unpack: unpacking ARP header\n");
	if (!arp) {
		if (WANT_DEBUG) fprintf(stderr, "arp_unack: no ARP structure specified; allocating one\n");
		arp = calloc(1, sizeof(struct ether_arp));
		if (!arp) {
			perror("failed to allocate ARP header structure");
			return NULL;
		}
	}

	memcpy(&u16, data, 2); arp->arp_hrd = ntohs(u16); data += 2;
	memcpy(&u16, data, 2); arp->arp_pro = ntohs(u16); data += 2;
	arp->arp_hln = data[0]; data++;
	arp->arp_pln = data[0]; data++;
	memcpy(&u16, data, 2); arp->arp_op = ntohs(u16); data += 2;

	if (arp->arp_op != ARPOP_REPLY)
		return NULL;

	memcpy(arp->arp_sha, data, arp->arp_hln); data += arp->arp_hln;
	memcpy(arp->arp_spa, data, arp->arp_pln); data += arp->arp_pln;

	memcpy(arp->arp_tha, data, arp->arp_hln); data += arp->arp_hln;
	memcpy(arp->arp_tpa, data, arp->arp_pln); data += arp->arp_pln;

	return arp;
}

static void
send_arp_request(struct in_addr *ip)
{
	uint8_t frame[IP_MAXPACKET] = {0};
	if (WANT_INFO) fprintf(stderr, "Sending ARP request to %s\n", inet_ntoa(*ip));

	memcpy(ARP.arp_tpa, &ip->s_addr, 4);

	/* Build the Ethernet frame:
	   [ dMAC | sMAC | TYPE | frame ... ] */
	memcpy(frame + 0, ARP.arp_tha, 6);
	memcpy(frame + 6, ARP.arp_sha, 6);
	frame[12] = 0x08; frame[13] = 0x06; /* ARP */
	if (!arp_pack(&ARP, frame + 14)) {
		if (WANT_DEBUG) perror("Failed to pack ARP header");
		return;
	}

	/* Send the Ethernet frame */
	if (WANT_TRACE) {
		fprintf(stderr, "Sending Ethernet frame:\n");
		dump(frame, 14 + ARP_HDRLEN);
	}
	sendto(SOCK, frame, 14 + ARP_HDRLEN, 0,
	       (struct sockaddr*)(&LL), sizeof(LL));
}

static void
recv_arp_replies(uint32_t timeout)
{

#define USEC(x) ((x).tv_sec * ONE_SEC + (x).tv_usec)
#define SINCE(a,b) (USEC(b) - USEC(a))
#define TIME(x) do { if (gettimeofday(&(x), NULL) != 0) { return; } } while (0)

	int rc;
	size_t n;
	struct timeval tv, last;
	uint8_t frame[IP_MAXPACKET] = {0};

	if (WANT_DEBUG) fprintf(stderr, "Setting socket recv timeout to 0.05s\n");
	tv.tv_sec = 0; tv.tv_usec = 50 * 1000;
	if ((rc = setsockopt(SOCK, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof(tv))) != 0) {
		DEBUG_RC("recv_arp_replies", "setsockopt()", rc);
		perror("failed to set receive timeout on socket");
		return;
	}

	TIME(last);
	while (1) {
		TIME(tv);
		if (SINCE(last, tv) > timeout) {
			if (WANT_INFO) fprintf(stderr, "%0.1fms since last ARP reply; exiting\n", SINCE(last, tv) / 1000.0);
			break;
		}

		memset(&frame, 0, 14 + ARP_HDRLEN);
		errno = 0;
		n = recvfrom(SOCK, &frame, IP_MAXPACKET, 0, NULL, 0);
		if (errno == EWOULDBLOCK || errno == EAGAIN) {
			continue;
		}
		if (n <= 0) {
			DEBUG_RC("recv_arp_replies", "recvfrom()", n);
			perror("recvfrom");
			break;
		}
		if (WANT_TRACE) {
			fprintf(stderr, "Read %i octets from socket\n", (int)n);
			fprintf(stderr, "Recevied Ethernet Frame\n");
			fprintf(stderr, " first 64 octets are:\n");
			dump(frame, 64);
		}

		if (!arp_unpack(frame + 14, &ARP)) {
			if (WANT_DEBUG) fprintf(stderr, "Failed to unpack ARP header; may not be an ARP reply\n");
			continue;
		}
		if (WANT_INFO) fprintf(stderr, "Received ARP reply\n");

		TIME(last);

		fprintf(stdout, ETHER_MAC_FMT " " IPv4_ADDR_FMT "\n",
			/* Ethernet MAC */
			(uint8_t)(ARP.arp_sha[0]), (uint8_t)(ARP.arp_sha[1]),
			(uint8_t)(ARP.arp_sha[2]), (uint8_t)(ARP.arp_sha[3]),
			(uint8_t)(ARP.arp_sha[4]), (uint8_t)(ARP.arp_sha[5]),

			/* IPv4 address */
			(uint8_t)(ARP.arp_spa[0]), (uint8_t)(ARP.arp_spa[1]),
			(uint8_t)(ARP.arp_spa[2]), (uint8_t)(ARP.arp_spa[3]));
	}

#undef USEC
#undef TIME
#undef SINCE

}

static void show_help(void);
static void show_version(void);
static void show_usage(const char*);

int
main(int argc, char **argv)
{
	int rc, opt, idx;
	const char *short_opts = "h?Vvqd:n:t:";
	struct option long_opts[] = {
		{ "help",    no_argument,       NULL, 'h' },
		{ "version", no_argument,       NULL, 'V' },
		{ "verbose", no_argument,       NULL, 'v' },
		{ "quiet",   no_argument,       NULL, 'q' },
		{ "device",  required_argument, NULL, 'd' },
		{ "network", required_argument, NULL, 'n' },
		{ "timeout", required_argument, NULL, 't' },
		{ 0, 0, 0, 0 },
	};
	while ( (opt = getopt_long(argc, argv, short_opts, long_opts, &idx)) != -1) {
		switch (opt) {
		case 'h':
		case '?':
			show_help();
			exit(0);

		case 'V':
			show_version();
			exit(0);

		case 'v':
			OPTIONS.debug++;
			break;

		case 'q':
			OPTIONS.debug = 0;
			break;

		case 'd':
			free(OPTIONS.device);
			OPTIONS.device = strdup(optarg);
			break;

		case 'n':
			free(OPTIONS.network);
			OPTIONS.network = strdup(optarg);
			break;

		case 't':
			OPTIONS.timeout = atoi(optarg);
			/* FIXME: use strto* and catch errors */
			break;
		}
	}

	/* FIXME: handle positionals properly */
	if (!OPTIONS.device || !OPTIONS.network) {
		show_usage("Missing -d and/or -n");
		return 1;
	}

	if (WANT_INFO) fprintf(stderr, "arpscan v" VERSION " starting up.\n");
	if (WANT_DEBUG) {
		fprintf(stderr, "  - device:  %s\n", OPTIONS.device);
		fprintf(stderr, "  - network: %s\n", OPTIONS.network);
		fprintf(stderr, "  - timeout: %ims\n", OPTIONS.timeout);
	}

	if (WANT_DEBUG) fprintf(stderr, "Setting up template ARP packet\n");
	if ((rc = arp_from(OPTIONS.device, &ARP, &LL)) != 0) {
		DEBUG_RC("main", "arp_from()", rc);
		fprintf(stderr, "Failed to set up for ARP from %s\n", OPTIONS.device);
		return 1;
	}

	/* Get a socket we can write a RAW Ethernet frame too */
	/* http://www.iana.org/assignments/ethernet-numbers */
	if (WANT_INFO) fprintf(stderr, "Acquiring raw/packet socket\n");
	SOCK = socket(PF_PACKET, SOCK_RAW, 0x0300);
	if (SOCK < 0) {
		DEBUG_RC("main", "socket()", SOCK);
		perror("failed to aquire a raw socket");
		return 1;
	}

	/* target MAC empty (ff:ff:ff:ff:ff:ff) */
	memset(ARP.arp_tha, 0xff, ETHER_ADDR_LEN);
	ARP.arp_op = ARPOP_REQUEST;

	if (WANT_INFO) fprintf(stderr, "Scanning network %s\n", OPTIONS.network);
	for_each_ip(OPTIONS.network, send_arp_request);

	if (WANT_INFO) fprintf(stderr, "Preparing to receive ARP replies\n");
	recv_arp_replies(OPTIONS.timeout * 1000);

	if (WANT_INFO) fprintf(stderr, "arpscan v" VERSION " shutting down\n");
	close(SOCK);
	return 0;
}

static void
show_help(void)
{
	printf("USAGE: arpscan [OPTIONS]\n"
	       "\n"
	       "  -h, --help            Show this helpful message.\n"
	       "                        (for more in-depth help, check the man page.)\n"
	       "\n"
	       "  -d, --device NAME     The interface to send ARP requests from.\n"
	       "\n"
	       "  -n, --network CIDR    Network range to scan, in CIDR notation\n"
	       "\n"
	       "  -t, --timeout MS      Number of milliseconds to wait on an ARP reply\n"
	       "                        before exiting.  Defaults to 500ms\n"
	       "\n");
}

static void
show_version(void)
{
	printf("arpscan v" VERSION "\n"
	       "Copyright 2014 James Hunt\n");
}

static void
show_usage(const char *msg)
{
	printf("Usage: arpscan -d <device> -n <network>\n");
	if (msg) printf("  %s\n", msg);
}
