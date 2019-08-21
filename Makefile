IXFREE := lib/ixfree
CPDT := lib/cpdt
TLC := lib/tlc

all: abseff

abseff: ixfree cpdt tlc Makefile.coq

Makefile.coq: _CoqProject
ifeq ($(wildcard Makefile.coq),)
	coq_makefile -f _CoqProject -o Makefile.coq
else
endif

include Makefile.coq

ixfree:
	$(MAKE) -C $(IXFREE)

cpdt:
	$(MAKE) -C $(CPDT)

tlc:
	$(MAKE) -C $(TLC)

clean::
	rm -f Makefile.coq Makefile.coq.bak

cleanall::
	$(MAKE) -C $(IXFREE) clean
	$(MAKE) -C $(CPDT) clean
	$(MAKE) -C $(TLC) clean

.PHONY: abseff ixfree cpdt tlc
