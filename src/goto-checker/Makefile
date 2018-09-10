SRC = bmc_util.cpp \
      goto_checker.cpp \
      goto_verifier.cpp \
      properties.cpp \
      solver_factory.cpp \
      property_checker.cpp \
      safety_checker.cpp \
      # Empty last line

INCLUDES= -I ..

include ../config.inc
include ../common

CLEANFILES = goto-checker$(LIBEXT)

all: goto-checker$(LIBEXT)

###############################################################################

goto-checker$(LIBEXT): $(OBJ)
	$(LINKLIB)
