# Builds the vellvm modules this project depends on, then this project.

VELLVM_SRC := vellvm/src

# Vellvm modules to build, relative to $(VELLVM_SRC). Add e.g. rocq/Semantics.vo
# here before importing Vellvm.Semantics.
VELLVM_TARGETS := rocq/Syntax.vo

.PHONY: all vellvm clean

all: vellvm Makefile.rocq
	$(MAKE) --no-print-directory -f Makefile.rocq

vellvm:
	$(MAKE) --no-print-directory -C $(VELLVM_SRC) RocqMakefile
	$(MAKE) --no-print-directory -C $(VELLVM_SRC) -f RocqMakefile $(VELLVM_TARGETS)

Makefile.rocq: _RocqProject
	rocq makefile -f _RocqProject -o Makefile.rocq

# Cleans this project only; vellvm's build is left alone.
clean:
	if [ -f Makefile.rocq ]; then $(MAKE) --no-print-directory -f Makefile.rocq clean; fi
	rm -f Makefile.rocq Makefile.rocq.conf .Makefile.rocq.d
