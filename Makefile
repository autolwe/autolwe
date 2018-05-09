# --------------------------------------------------------------------
DESTDIR ?=
PREFIX  ?= /usr/local
VERSION ?= $(shell date '+%F')
INSTALL := scripts/install/install-sh
PWD     := $(shell pwd)
BINDIR  := $(PREFIX)/bin
LIBDIR  := $(PREFIX)/lib/autognp
SHRDIR  := $(PREFIX)/share/autognp
INSTALL := scripts/install/install-sh
UNAME_S := $(shell uname -s)

CPPFLAGS ?=
CXXFLAGS ?= -I/usr/local/include -I/opt/local/include
LDFLAGS  ?= -L/opt/local/lib

# --------------------------------------------------------------------
LIBFLAGS := $(LDFLAGS:%=-lflags -cclib,%)

ifeq ($(UNAME_S),Linux)
  LIBFLAGS += -lflags -cclib,-Xlinker,-cclib,--no-as-needed
endif
ifeq ($(UNAME_S),Darwin)
  LIBFLAGS +=
endif

LIBFLAGS += -lflags -cclib,-Lc_src,-cclib,-lfactory,-cclib,-lfactorystubs

# --------------------------------------------------------------------
OCAMLBUILDFLAGS=-use-ocamlfind -cflags "-w +a-e-9-44-48-37"

ifeq ($(shell echo $$TERM), dumb)
 OCAMLBUILDFLAGS += -classic-display -quiet
endif

# --------------------------------------------------------------------
.PHONY: clean all doc test test autognp wsautognp
.PHONY: autognp.native wsautognp.native

all: autognp.native

autognp.native: stubs
	ocamlbuild $(LIBFLAGS) $(OCAMLBUILDFLAGS) autognp.native

install:
	$(INSTALL) -m 0755 -d $(DESTDIR)$(BINDIR)
	$(INSTALL) -m 0755 -T autognp.native $(DESTDIR)$(BINDIR)/autognp

uninstall:
	rm -f $(DESTDIR)$(BINDIR)/autognp

clean:
	ocamlbuild -clean
	-@rm -rf tutor.docdir

factory: stubs
	ocamlbuild $(LIBFLAGS) $(OCAMLBUILDFLAGS) Factory.native

wsautognp.native: stubs
	ocamlbuild $(LIBFLAGS) $(OCAMLBUILDFLAGS) wsautognp.native

# --------------------------------------------------------------------
STUB_SRC   := c_src
STUB_BLD   := _build/$(STUB_SRC)
STUB_OBJS  := factory_stubs.o
STUB_LIBA  := libfactorystubs.a
STUB_LIBSO := libfactorystubs.so

stubs: $(STUB_BLD) $(STUB_BLD)/$(STUB_LIBA) $(STUB_BLD)/$(STUB_LIBSO)
	@true

$(STUB_BLD):
	mkdir -p $(STUB_BLD)

$(STUB_BLD)/%.o: $(STUB_SRC)/%.cc
	$(CXX) $(CPPFLAGS) $(CXXFLAGS) -fPIC -c -o $@ $<

$(STUB_BLD)/$(STUB_LIBA): $(STUB_OBJS:%=$(STUB_BLD)/%)
	rm -f $@ && ar rc $@ $^ && ranlib $@

$(STUB_BLD)/$(STUB_LIBSO): $(STUB_OBJS:%=$(STUB_BLD)/%)
	$(CXX) $(LDFLAGS) -shared -lfactory -o $@ $^

# --------------------------------------------------------------------
# Used for development and testing

.PHONY: Test_Util Test_Type Test_Expr Test_Norm Test_Cpa Test_Parser Test_Web

dev: stubs
	ocamlbuild $(LIBFLAGS) $(OCAMLBUILDFLAGS) Game.cma

dev_server: wsautognp.native
	-@ killall wsautognp.native

%.deps:
	ocamlfind ocamldep -package bolt -package batteries -syntax camlp4o \
            -package comparelib.syntax \
            -I src/CAS -I src/Expr -I src/Extract -I src/Game -I src/Deduce -I src/Main \
            -I src/Parser -I src/Poly -I src/Norm -I src/Derived -I src/Core \
            -I src/Engine -I src/Util \
            one-line src/$(basename $@).ml> .depend
	ocamldot .depend > deps.dot
	dot -Tsvg deps.dot >deps.svg

depgraph:
	ocamlfind ocamldep -package bolt -package batteries -syntax camlp4o \
            -package comparelib.syntax \
            -I src/CAS -I src/Expr -I src/Extract -I src/Game -I src/Deduce -I src/Main \
            -I src/Parser -I src/Poly -I src/Norm -I src/Derived -I src/Core \
            -I src/Engine -I src/Util \
            one-line src/**/*.ml src/**/*.mli \
        | grep -v Test | grep -v Extract > .depend
	ocamldot .depend > deps.dot
	dot -Tsvg deps.dot >deps.svg


autognp.native-dev: stubs
	ocamlbuild $(LIBFLAGS) $(OCAMLBUILDFLAGS) autognp.native
	rm autognp.log
	BOLT_CONFIG=log_bolt.config ./autognp.native test.zc ; cat autognp.log

wsautognp.native-dev: wsautognp.native
	-@killall wsautognp.native

test-examples: autognp.native
	bash scripts/run_tests.sh

test-examples-ec: autognp.native
	bash scripts/run_examples_ec.sh

test-tests-ec: autognp.native
	bash scripts/run_tests_ec.sh

Test_Type:
	ocamlbuild $(OCAMLBUILDFLAGS) Test_Type.d.byte && ./Test_Type.d.byte

Test_Expr:
	ocamlbuild $(OCAMLBUILDFLAGS) Test_Expr.d.byte && ./Test_Expr.d.byte

Test_Singular:
	ocamlbuild $(OCAMLBUILDFLAGS) Test_Singular.d.byte && ./Test_Singular.d.byte

Test_Pretty_Expr:
	ocamlbuild $(OCAMLBUILDFLAGS) Test_Pretty_Expr.d.byte && ./Test_Pretty_Expr.d.byte

Test_Solve_Fq:
	ocamlbuild $(OCAMLBUILDFLAGS) Test_Solve_Fq.d.byte && ./Test_Solve_Fq.d.byte

%.inferred.mli:
	ocamlbuild $(OCAMLBUILDFLAGS) src/$@ && cat _build/src/$@

stubtest:
	c++ c_src/factory_stubs.cc -o factory_test -I/usr/local/include/factory -DWITHMAIN -lfactory 
	./factory_test

