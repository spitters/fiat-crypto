#!/usr/bin/env python3
"""Selective inlining: only inline Fp base ops into Fp2 ops.

The key insight: inlining Fp-level add/sub/mul/opp into Fp2-level
functions lets GCC optimize across the Fp2 Karatsuba pattern without
the overhead of full tower inlining.

Usage: python3 apply_restrict.py < input.c > output.c
"""
import sys
import re

# Only inline base Fp ops (small functions, good for register allocation)
INLINE_FNS = {
    'bls24_509_add', 'bls24_509_sub', 'bls24_509_mul',
    'bls24_509_square', 'bls24_509_opp', 'bls24_509_felem_copy',
    'bls24_Fp2_mul_by_nr',
}

def transform(text):
    lines = text.split('\n')
    result = []

    for line in lines:
        # For function definitions of INLINE_FNS, add always_inline
        m = re.match(r'^(void (\w+)\([^)]*\)) \{', line)
        if m and m.group(2) in INLINE_FNS:
            result.append(f'__attribute__((always_inline)) static inline {m.group(1)} {{')
            continue
        # For forward declarations of INLINE_FNS, mark static inline
        m2 = re.match(r'^(void (\w+)\([^)]*\));', line)
        if m2 and m2.group(2) in INLINE_FNS:
            result.append(f'static inline {m2.group(1)};')
            continue
        result.append(line)

    return '\n'.join(result)


if __name__ == '__main__':
    print(transform(sys.stdin.read()))
