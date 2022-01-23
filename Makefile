# This is the main Makefile #
#############################

# I usually prefer to rule out OSX make on the basis that it doesn't have the
# shortest stem rule, which is incredibly useful.
ifeq (3.81,$(MAKE_VERSION))
  $(error You seem to be using the OSX antiquated Make version. Hint: brew \
    install make, then invoke gmake instead of make)
endif


# Main entry points (first one is default)
# ----------------------------------------

.PHONY: clean
all: dist/libz.a

.PHONY: clean
clean:
	rm -rf dist/* obj/*

include Makefile.include

# Definition of F* flags
# ----------------------

FSTAR_HINTS ?= --use_hints --use_hint_hashes --record_hints

# This flag controls what gets extracted to OCaml. Generally, we don't extract
# the FStar namespace since it's already extracted and packaged as the ocamlfind
# package fstarlib. Here, unlike in -bundle, +Spec matches both Spec and
# Spec.*
FSTAR_EXTRACT = --extract 'Kremlin:Yazi' \
	--extract 'Kremlin:FStar' \
	--extract 'Kremlin:LowStar' \
	--extract "-*"

# Some reasonable flags to turn on:
# - 247: checked file not written because some of its dependencies...
# - 285: missing or file not found, almost always something to act on
# - 241: stale dependencies, almost always a sign that the build is incorrect
#
# But also:
# - --cmi, for cross-module inlining, a must-have for anyone who relies on
#   inline_for_extraction in the presence of interfaces
# - --cache_checked_modules to rely on a pre-built ulib and kremlib
# - --cache_dir, to avoid polluting our generated build artifacts outside o
FSTAR_NO_FLAGS = $(FSTAR_HOME)/bin/fstar.exe $(FSTAR_HINTS) \
  --odir obj --cache_checked_modules $(FSTAR_INCLUDES) --cmi \
  --already_cached 'Prims FStar LowStar TestLib' --warn_error '+241@247+285' \
  --cache_dir obj \
  --hint_dir hints \
  --z3rlimit 120

# Initial dependency analysis
# ---------------------------

# Important to wildcard both fst and fsti since there are fstis without fsts,
# etc. Note that I'm using wildcard rather than assume $(SHELL) is bash and has
# fancy globbing rules -- particularly true on Windows.
FSTAR_ROOTS = $(wildcard $(addsuffix /*.fsti,$(SOURCE_DIRS))) \
  $(wildcard $(addsuffix /*.fst,$(SOURCE_DIRS))) \


# This is the only bulletproof way that I know of forcing a regeneration of the
# .depend file every single time. Why, you may ask? Well, it's frequent enough
# to add a new file that you don't want to decipher a cryptic error only to
# remember you should run `make depend`. Also, if you move files around, it's
# good to force regeneration even though .depend may be more recent than the
# mtime of the moved files.
ifndef MAKE_RESTARTS
.depend: .FORCE
	$(FSTAR_NO_FLAGS) --dep full $(notdir $(FSTAR_ROOTS)) $(FSTAR_EXTRACT) > $@

.PHONY: .FORCE
.FORCE:
endif

include .depend

# Verification
# ------------

# Everest-specific idiom: all makefiles accept OTHERFLAGS, for instance, if one
# wants to rebuild with OTHERFLAGS="--admit_smt_queries true". We just don't
# pass such flags to the dependency analysis.
FSTAR = $(FSTAR_NO_FLAGS) $(OTHERFLAGS)

# Creating these directories via a make rule, rather than rely on F* creating
# them, as two calls to F* might race.
hints:
	mkdir $@

obj:
	mkdir $@

# We allow some specific pattern rules to be added here, relying on the shortest
# stem rule for them to take precedence. For instance, you may want to do:
#
# obj/Bignum.Impl.fst.checked: FSTAR_FLAGS = "--query_stats"
#
# (Note: for options that control the SMT encoding, such as
# --smtencoding.nl_arith_repr native, please make sure you also define them in
# Makefile.common for %.fst-in otherwise you'll observe different behaviors
# between interactive and batch modes.)
#
# By default, however, variables are inherited through the dependencies, meaning
# that the example above would normally set these FSTAR_FLAGS for any .checked
# that is rebuilt because it's a dependency of Bignum.Impl.fst.checked.
#
# To avoid this unpleasant behavior, the most general pattern rule (longest
# stem) also defines a suitable default value for FSTAR_FLAGS.
# %.checked: FSTAR_FLAGS=

# Note: F* will not change the mtime of a checked file if it is
# up-to-date (checksum matches, file unchanged), but this will confuse
# make and result in endless rebuilds. So, we touch that file.
%.checked: | hints obj
	$(FSTAR) $< $(FSTAR_FLAGS) && touch -c $@

# Extraction
# ----------
.PRECIOUS: obj/%.krml
obj/%.krml:
	$(FSTAR) $(notdir $(subst .checked,,$<)) --codegen Kremlin \
	--extract_module $(basename $(notdir $(subst .checked,,$<)))

KRML=$(KREMLIN_HOME)/krml

# Note: the implementation of the intrinsic uses external linkage, but you could
# easily turn this file into a .h, use -add-include '"Impl_Bignum_Intrinsics.h"'
# and pass -static-header Impl.Bignum.Intrinsics as described in the
# documentation.
HAND_WRITTEN_C_FILES = code/c/Yazi_Misc.h code/c/Yazi_Z_Stream_Fields.inc code/c/Yazi_CRC32_Z.inc code/c/Yazi_Adler32_Z.inc

# This is now the preferred and recommended way to compile C code with KreMLin.
#
# KreMLin (via -skip-compilation) only generates a stub Makefile in dist/,
# instead of acting as a C compilation driver like it did before. The Makefile
# that is generated by KreMLin is basic, but takes into account:
# - the -o option to determine what is being built
# - the C files passed on the command line, which will be linked together
# - C compiler flags passed to KreMLin via -ccopts
#
# This Makefile is called Makefile.basic and should be enough for all your basic
# needs. If you need something more fancy, you can easily author your own custom
# dist/Makefile, which includes Makefile.basic, then proceeds to redefine /
# tweak some variables.
#
# Note that you are of course more than welcome to define your own
# CMakeLists.txt or whatever your favorite build system is: this tutorial only
# describes the supported canonical way of compiling code.
#
# See the advanced topics section for an in-depth explanation of how the -bundle
# option works. We also use -minimal.
dist/Makefile.basic: $(filter-out %prims.krml,$(ALL_KRML_FILES)) $(HAND_WRITTEN_C_FILES) $(ALL_CHECKED_FILES)
	mkdir -p $(dir $@)
	cp $(HAND_WRITTEN_C_FILES) $(dir $@)
	$(KRML) -tmpdir $(dir $@) -skip-compilation \
	  $(filter %.krml,$^) \
	  -warn-error @4@5@18 \
	  -no-prefix Yazi.Adler32 \
	  -no-prefix Yazi.CFlags \
	  -no-prefix Yazi.CRC32 \
	  -no-prefix Yazi.CRC32.* \
	  -no-prefix Yazi.LZ77 \
	  -no-prefix Yazi.Util \
	  -no-prefix Yazi.Tree \
	  -no-prefix Yazi.Tree.* \
	  -no-prefix Yazi.Types \
	  -fextern-c \
	  -ftail-calls \
	  -fparentheses \
	  -fcurly-braces \
	  -fc89 \
	  -minimal \
	  -drop LowStar.ConstBuffer,C.Loops,Spec.*,Prims,Lib.*\
	  -bundle 'FStar.*' \
	  -bundle Yazi.LZ77=Yazi.LZ77,Yazi.LZ77.*,Yazi.Stream.State \
	  -bundle Yazi.CRC32=Yazi.CRC32,Yazi.CRC32.* \
	  -bundle Yazi.Tree=Yazi.Tree,Yazi.Tree.* \
	  -add-include '<stdint.h>' \
	  -add-include '<string.h>' \
	  -add-early-include '"Yazi_Misc.h"' \
	  -add-include '"kremlin/internal/target.h"' \
	  -o libz.a
	sed -i \
          '/deflate_state \*state;.*/a #include "Yazi_Z_Stream_Fields.inc"' \
	  dist/Yazi_Types.h
	sed -i \
          '/adler32_z/c\#include "Yazi_Adler32_Z.inc"' \
	  dist/Yazi_Adler32.c

# Compiling the generated C code
# ------------------------------

# Here we do a recursive make invocation because a new dependency analysis needs
# to be performed on the generated C files. This recursive make deals with all
# the files copied in dist, which includes kremlin-generated and hand-written,
# copied files from HAND_WRITTEN_C_FILES.

crc32_table_gen: dist/Makefile.basic
	cc -I ./dist \
	   -I $(KREMLIN_HOME)/include \
	   -I $(KREMLIN_HOME)/kremlib/dist/minimal \
	   -D YAZI_CRC32_TABLE_GEN \
	   code/c/Yazi_CRC32_Table_Codegen.c dist/Yazi_CRC32.c\
	   -g -o ./dist/crc32_table_gen
	./dist/crc32_table_gen > ./dist/Yazi_CRC32_Table.inc
	sed -i \
          '/Yazi_CRC32.h/c\#include "Yazi_CRC32_Table.inc"' \
	  dist/Yazi_CRC32.c
	rm ./dist/crc32_table_gen

dist/libz.a: dist/Makefile.basic crc32_table_gen
	$(MAKE) -C $(dir $@) -f $(notdir $<)

