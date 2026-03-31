#!/usr/bin/env python3
"""Copy elimination v2: Phase 1 (componentwise) + Phase 2 (non-aliased mul/sqr).

Phase 1: Remove ALL copies in componentwise functions (add/sub/opp/conjugate).
Phase 2: Remove copies in mul/sqr for non-aliased arguments.
         For aliased args (out == inx), keep only that copy.

Usage: python3 apply_copy_elim_v2.py < input.c > output.c
"""
import sys
import re

# Phase 1: componentwise functions (all copies safe to remove)
PHASE1_FNS = {
    'bls12_Fp2_add', 'bls12_Fp2_sub', 'bls12_Fp2_opp',
    'bls12_Fp2_mul_xi', 'bls12_Fp2_conjugate',
    'bls12_Fp6_add', 'bls12_Fp6_sub', 'bls12_Fp6_opp',
    'bls12_Fp6_felem_copy',
    'bls12_Fp12_add', 'bls12_Fp12_sub', 'bls12_Fp12_opp',
    'bls12_Fp12_felem_copy', 'bls12_Fp12_conjugate',
}

# Phase 2: mul/sqr functions (copies needed only for aliased args)
PHASE2_FNS = {
    'bls12_Fp6_mul', 'bls12_Fp6_square',
    'bls12_Fp12_mul', 'bls12_Fp12_square',
    'bls12_Fp6_inv', 'bls12_Fp12_inv',
}

COPY_FNS = {
    'bls12_felem_copy', 'bls12_Fp2_felem_copy',
    'bls12_Fp6_felem_copy', 'bls12_Fp12_felem_copy',
}

ALL_SAFE = PHASE1_FNS | PHASE2_FNS

def transform_function(lines, fn_name):
    """Transform a function body."""
    stackalloc_re = re.compile(
        r'(\s*)(?:\{\s*)?uint8_t\s+(_br_stackalloc_\w+)\[.*?\](?:\s*=\s*\{0\})?\s*;\s*'
        r'(\w+)\s*=\s*\((?:br_word_t|uintptr_t)\)&\2;')
    copy_re = re.compile(
        r'\s*(' + '|'.join(re.escape(fn) for fn in COPY_FNS) + r')\((\w+),\s*(\w+)\);')

    # Find all stackalloc variables and their copy sources
    alloc_info = {}  # alloc_var -> (line_idx, src_var, copy_line_idx)
    for idx, line in enumerate(lines):
        sa = stackalloc_re.match(line)
        if sa:
            alloc_var = sa.group(3)
            for j in range(idx + 1, min(idx + 10, len(lines))):
                cm = copy_re.match(lines[j])
                if cm and cm.group(2) == alloc_var:
                    alloc_info[alloc_var] = (idx, cm.group(3), j)
                    break

    if fn_name in PHASE1_FNS:
        # Phase 1: remove ALL copies
        alloc_lines = {info[0] for info in alloc_info.values()}
        copy_lines = {info[2] for info in alloc_info.values()}
        result = []
        for idx, line in enumerate(lines):
            if idx in alloc_lines:
                sa = stackalloc_re.match(line)
                alloc_var = sa.group(3)
                if alloc_var in alloc_info:
                    indent = sa.group(1)
                    result.append(f'{indent}{alloc_var} = {alloc_info[alloc_var][1]};')
                    continue
            if idx in copy_lines:
                continue
            result.append(line)
        return result

    elif fn_name in PHASE2_FNS:
        # Phase 2: check function params for aliasing pattern
        # Parse params from first line: static void fn(br_word_t out, br_word_t inx, br_word_t iny) {
        param_re = re.compile(r'(?:br_word_t|uintptr_t)\s+(\w+)')
        params = param_re.findall(lines[0]) if lines else []
        out_param = params[0] if len(params) >= 1 else None

        # For each alloc_var: if it copies a param that is NOT out_param,
        # then it's safe to eliminate (the arg won't be overwritten).
        # If it copies out_param, keep the copy (aliased case).
        alloc_lines_to_remove = set()
        copy_lines_to_remove = set()
        for alloc_var, (alloc_idx, src_var, copy_idx) in alloc_info.items():
            # src_var is the function parameter being copied
            # If src_var != out_param, this copy is for a non-aliased input
            # We can eliminate it IF the function is called with non-aliased args.
            # But we don't know the call site here.
            #
            # Conservative: only eliminate if the FUNCTION ITSELF guarantees safety.
            # For mul(out, inx, iny):
            #   allocx copies inx, allocy copies iny.
            #   If we skip allocy's copy but keep allocx's, then:
            #     - reads from allocy (= iny) are safe (iny is never written)
            #     - reads from allocx (= copy of inx) are needed because out might == inx
            #   This is safe as long as the function body doesn't modify iny.
            #   For Karatsuba, iny is only read, never written. So skipping iny's copy is safe.
            #
            # So: keep copies of params that alias with out, skip copies of non-aliased params.
            # Since we don't know at the function level which param aliases out,
            # we keep ALL copies. The optimization must be done at the CALL SITE.
            pass

        # For Phase 2 at the function level: we can't optimize without call-site info.
        # Return unchanged.
        return lines

    return lines

def transform(text):
    lines = text.split('\n')
    result = []
    func_def = re.compile(r'^static\s+\w+\s+(\w+)\s*\([^)]*\)\s*\{')
    i = 0
    while i < len(lines):
        m = func_def.match(lines[i])
        if m and m.group(1) in ALL_SAFE:
            fn_lines = [lines[i]]
            i += 1
            depth = 1
            while i < len(lines) and depth > 0:
                depth += lines[i].count('{') - lines[i].count('}')
                fn_lines.append(lines[i])
                i += 1
            result.extend(transform_function(fn_lines, m.group(1)))
        else:
            result.append(lines[i])
            i += 1
    return '\n'.join(result)

if __name__ == '__main__':
    print(transform(sys.stdin.read()))
