# Comment out the below line if you want to be quiet by default.
V=1

# Specify a number of jobs
JOBS=-j4

ifeq ($(V),1)
E=@true
Q=
MFLAGS=$(JOBS)
else
E=@echo
Q=@
MFLAGS=$(JOBS) -s
endif

SRCS := $(wildcard *.knot)
VS   := $(SRCS:.knot=.v)
AUXS := $(join $(dir $(SRCS)), $(addprefix ., $(notdir $(SRCS:.knot=.aux))))

.PHONY: coq clean

coq: Makefile.coq
	$(E) "  MAKE Makefile.coq"
	$(Q)$(MAKE) $(MFLAGS) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	$(E) "  COQ_MAKEFILE Makefile.coq"
	$(Q)coq_makefile -f _CoqProject -o Makefile.coq

clean: Makefile.coq
	$(Q)$(MAKE) $(MFLAGS) -f Makefile.coq clean
	$(Q)rm -f $(AUXS) .Needle.aux
	$(Q)rm -f Makefile.coq *.bak *.d *.glob *~ result*
	$(Q)rm -f *.desugared
	$(Q)rm -f $(VS)

%.v: %.knot
	$(Q)needle $<
