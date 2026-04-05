#!/usr/bin/env python3
"""Apply copy elimination to bedrock2-generated C code.

For each safe function, finds ALL stackalloc+copy pairs and eliminates them.
The pattern across a function body:
  uint8_t _br_stackalloc_VAR[N] = {0}; VAR = (br_word_t)&_br_stackalloc_VAR;
  ...
  COPY_FN(VAR, SRC);
becomes:
  VAR = SRC;

Usage: python3 apply_copy_elim.py < input.c > output.c
"""
import sys
import re

SAFE_FNS = {
    # BLS12-381
    'bls12_Fp2_add', 'bls12_Fp2_sub', 'bls12_Fp2_opp',
    'bls12_Fp2_mul_xi', 'bls12_Fp2_conjugate',
    'bls12_Fp6_add', 'bls12_Fp6_sub', 'bls12_Fp6_opp',
    'bls12_Fp6_felem_copy',
    'bls12_Fp12_add', 'bls12_Fp12_sub', 'bls12_Fp12_opp',
    'bls12_Fp12_felem_copy', 'bls12_Fp12_conjugate',
    # BLS24-509: componentwise ops (safe for copy elimination)
    'bls24_Fp2_add', 'bls24_Fp2_sub', 'bls24_Fp2_opp',
    'bls24_Fp2_felem_copy', 'bls24_Fp2_mul_xi',
    'bls24_Fp4_add', 'bls24_Fp4_sub', 'bls24_Fp4_opp',
    'bls24_Fp4_felem_copy', 'bls24_Fp4_mul_by_v',
    'bls24_Fp8_add', 'bls24_Fp8_sub', 'bls24_Fp8_opp',
    'bls24_Fp8_felem_copy', 'bls24_Fp8_mul_by_w',
    'bls24_Fp24_add', 'bls24_Fp24_sub', 'bls24_Fp24_opp',
    'bls24_Fp24_felem_copy', 'bls24_fp24_conjugate',
}

COPY_FNS = {
    'bls12_felem_copy', 'bls12_Fp2_felem_copy',
    'bls12_Fp6_felem_copy', 'bls12_Fp12_felem_copy',
    # BLS24-509
    'bls24_509_felem_copy', 'bls24_Fp2_felem_copy',
    'bls24_Fp4_felem_copy', 'bls24_Fp8_felem_copy',
    'bls24_Fp24_felem_copy',
}

def transform_function(lines):
    """Transform a safe function's body to eliminate stackalloc+copy."""
    # Phase 1: Find all stackalloc variables and their corresponding copies
    stackalloc_re = re.compile(
        r'(\s*)uint8_t\s+(_br_stackalloc_\w+)\[.*?\](?:\s*=\s*\{0\})?\s*;\s*'
        r'(\w+)\s*=\s*\((?:br_word_t|uintptr_t)\)&\2;')
    copy_re = re.compile(
        r'(\s*)(' + '|'.join(re.escape(fn) for fn in COPY_FNS) + r')\((\w+),\s*(\w+)\);')

    # Map: alloc_var -> source_var (from copy calls)
    alloc_to_src = {}
    alloc_lines = set()  # line indices of stackalloc lines
    copy_lines = set()   # line indices of copy lines

    for idx, line in enumerate(lines):
        sa = stackalloc_re.match(line)
        if sa:
            alloc_var = sa.group(3)
            alloc_lines.add(idx)
            # Look for the copy call for this variable in subsequent lines
            for j in range(idx + 1, min(idx + 10, len(lines))):
                cm = copy_re.match(lines[j])
                if cm and cm.group(3) == alloc_var:
                    alloc_to_src[alloc_var] = cm.group(4)
                    copy_lines.add(j)
                    break

    # Phase 2: Rewrite
    result = []
    for idx, line in enumerate(lines):
        if idx in alloc_lines:
            sa = stackalloc_re.match(line)
            alloc_var = sa.group(3)
            if alloc_var in alloc_to_src:
                indent = sa.group(1)
                result.append(f'{indent}{alloc_var} = {alloc_to_src[alloc_var]};')
                continue
        if idx in copy_lines:
            continue  # skip the copy call
        result.append(line)
    return result

def transform(text):
    lines = text.split('\n')
    result = []

    func_def = re.compile(r'^(?:static\s+)?void\s+(\w+)\s*\([^)]*\)\s*\{')
    i = 0

    while i < len(lines):
        m = func_def.match(lines[i])
        if m and m.group(1) in SAFE_FNS:
            # Collect the entire function body
            fn_lines = [lines[i]]
            i += 1
            depth = 1
            while i < len(lines) and depth > 0:
                depth += lines[i].count('{') - lines[i].count('}')
                fn_lines.append(lines[i])
                i += 1
            # Transform and emit
            result.extend(transform_function(fn_lines))
        else:
            result.append(lines[i])
            i += 1

    return '\n'.join(result)

if __name__ == '__main__':
    print(transform(sys.stdin.read()))
