#AUTOMAKE_OPTIONS = foreign subdir-objects

############################################################

AM_CFLAGS     = -Wall

############################################################

CLEANFILES       = $(BUILT_SOURCES)

man1_MANS = man/arpscan.1

############################################################

sbin_PROGRAMS = arpscan
arpscan_SOURCES = src/arpscan.c

install-exec-hook:
	chown root $(DESTDIR)$(sbindir)/arpscan
	chmod u+s $(DESTDIR)$(sbindir)/arpscan

############################################################

version:
	@echo $(VERSION)

distfile: dist
	@echo $(PACKAGE)-$(VERSION).tar.gz

manifest:
	@echo >&2 "nothin doin"
