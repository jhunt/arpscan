#AUTOMAKE_OPTIONS = foreign subdir-objects

############################################################

AM_CFLAGS = -Wall

CLEANFILES = $(BUILT_SOURCES)

dist_man_MANS = man/arpscan.1
sbin_PROGRAMS = arpscan
arpscan_SOURCES = src/arpscan.c

version:
	@echo $(VERSION)

distfile: dist
	@echo $(PACKAGE)-$(VERSION).tar.gz

manifest:
	@echo >&2 "nothin doin"
