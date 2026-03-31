CC      ?= gcc
CFLAGS  ?= -O2 -Wall -Wextra -Wno-unused-parameter -Wno-unused-function -std=c11
LDFLAGS ?=

.PHONY: all clean

all: bench_bls377

bench_bls377: bench_bls377.c bls377_pairing.c bls377_stubs.c bls377_pairing.h
	$(CC) $(CFLAGS) -o $@ bench_bls377.c $(LDFLAGS)

clean:
	rm -f bench_bls377
