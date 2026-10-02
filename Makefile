CC ?= cc
DEPS ?= $(CURDIR)/deps
CFLAGS ?= -O2 -std=c11 -D_POSIX_C_SOURCE=200809L -Wall -Wextra -Wno-unused-parameter -Wno-sign-compare
CPPFLAGS += -I$(DEPS)/include
LDLIBS = $(DEPS)/lib/msolve_main.o -L$(DEPS)/lib -lmsolve -lneogb -lflint -lmpfr -lgmp -lgomp -lm -lpthread
SRC = src/value.c src/account.c src/lang.c src/builtins.c src/msolve.c src/main.c
OBJ = $(SRC:.c=.o)

amath: $(OBJ)
	$(CC) $(CFLAGS) -static -s -Wl,--gc-sections -o $@ $(OBJ) $(LDLIBS)

src/%.o: src/%.c src/am.h src/msolve_bridge.h
	$(CC) $(CPPFLAGS) $(CFLAGS) -c -o $@ $<

# the engines, built once into deps/ as static libraries
FLINT_TAG = v3.3.1
MSOLVE_TAG = v0.9.0
deps:
	mkdir -p build-deps
	cd build-deps && [ -d flint ] || git clone -q --depth 1 --branch $(FLINT_TAG) https://github.com/flintlib/flint.git
	cd build-deps/flint && ./bootstrap.sh && ./configure --prefix=$(DEPS) --disable-shared --enable-static && $(MAKE) && $(MAKE) install
	cd build-deps && [ -d msolve ] || git clone -q --depth 1 --branch $(MSOLVE_TAG) https://github.com/algebraic-solving/msolve.git
	cd build-deps/msolve && ./autogen.sh && CPPFLAGS=-I$(DEPS)/include LDFLAGS=-L$(DEPS)/lib ./configure --prefix=$(DEPS) --disable-shared --enable-static && $(MAKE) && $(MAKE) install
	cd build-deps/msolve && $(CC) -O2 -c -Dmain=msolve_main -DVERSION='"$(MSOLVE_TAG)"' -I$(DEPS)/include -I. -Isrc src/msolve/main.c -o $(DEPS)/lib/msolve_main.o

test: amath
	sh tests/run.sh

clean:
	rm -f amath src/*.o

.PHONY: deps test clean
