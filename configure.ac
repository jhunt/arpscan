#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.

AC_PREREQ(2.68)
AC_INIT(arpscan, 1.0.1, james@jameshunt.us)
AC_CONFIG_SRCDIR([src])
AC_CONFIG_AUX_DIR([build])
AM_INIT_AUTOMAKE
AM_MAINTAINER_MODE

# Checks for programs.
AC_PROG_CC
AC_PROG_INSTALL

# Checks for header files.

AC_HEADER_STDC
AC_CHECK_HEADERS([\
	sys/types.h \
	sys/socket.h \
	sys/ioctl.h \
	sys/time.h \
	arpa/inet.h \
	net/if.h \
	net/if_arp.h \
	linux/if_packet.h \
	netinet/ip.h \
	netinet/ether.h])

# Checks for typedefs, structures, and compiler characteristics.

AC_C_INLINE

AC_TYPE_SIZE_T
AC_TYPE_SSIZE_T

AC_TYPE_UINT8_T
AC_TYPE_UINT16_T
AC_TYPE_UINT32_T

# Checks for library functions.
AC_PROG_GCC_TRADITIONAL
AC_CHECK_FUNCS([memset socket gettimeofday])

AC_OUTPUT(Makefile)


echo "
  $PACKAGE_NAME version $PACKAGE_VERSION
  Prefix.........: $prefix
  C Compiler.....: $CC $CFLAGS $CPPFLAGS
  Linker.........: $LD $LDFLAGS $LIBS
"
