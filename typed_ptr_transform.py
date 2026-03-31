#!/usr/bin/env python3
"""Transform bedrock2 C: change function parameters to uint8_t *restrict.

Keep br_word_t = uintptr_t for local variables and values.
Only change function PARAMETER types to uint8_t *restrict.
At call sites, cast uintptr_t locals to uint8_t* when passing.

This gives GCC restrict info across function boundaries while keeping
the internal integer arithmetic unchanged.
"""
import sys
import re

def transform(text):
    lines = text.split('\n')
    result = []

    # Step 1: Change _br_load/_br_store address parameters
    new_lines = []
    for line in lines:
        # _br_load(uintptr_t a, ...) -> _br_load(const uint8_t *restrict a, ...)
        line = re.sub(
            r'_br_load\(uintptr_t a\)',
            '_br_load(const uint8_t *restrict a)',
            line)
        line = re.sub(
            r'_br_load\(uintptr_t a, uintptr_t sz\)',
            '_br_load(const uint8_t *restrict a, uintptr_t sz)',
            line)
        # _br_store(uintptr_t a, ...) -> _br_store(uint8_t *restrict a, ...)
        line = re.sub(
            r'_br_store\(uintptr_t a, uintptr_t v\)',
            '_br_store(uint8_t *restrict a, uintptr_t v)',
            line)
        line = re.sub(
            r'_br_store\(uintptr_t a, uintptr_t v, uintptr_t sz\)',
            '_br_store(uint8_t *restrict a, uintptr_t v, uintptr_t sz)',
            line)
        # Remove (void*) casts in load/store bodies — a is already uint8_t*
        line = line.replace('memcpy(&r, (void*)a,', 'memcpy(&r, a,')
        line = line.replace('memcpy((void*)a, &v,', 'memcpy(a, &v,')
        line = line.replace('memcpy(&r, (void *)a,', 'memcpy(&r, a,')
        line = line.replace('memcpy((void *)a, &v,', 'memcpy(a, &v,')
        line = line.replace('return *((uint8_t *)a);', 'return *a;')
        new_lines.append(line)
    lines = new_lines

    # Step 2: Change function parameter types: br_word_t -> uint8_t *restrict
    # But NOT for return types or local variables.
    # Pattern: function decl/def has (br_word_t param, br_word_t param, ...)
    func_param_re = re.compile(r'^(static\s+(?:void|uintptr_t|br_word_t)\s+\w+\s*\()(.+?)(\)\s*[;{])')

    new_lines = []
    for line in lines:
        m = func_param_re.match(line)
        if m:
            prefix, params, suffix = m.group(1), m.group(2), m.group(3)
            # Skip _br_load/_br_store (already handled)
            if '_br_load' in prefix or '_br_store' in prefix or '_br2_load' in prefix or '_br2_store' in prefix:
                new_lines.append(line)
                continue
            # Replace br_word_t with uint8_t *restrict in params
            # But keep br_word_t* (return pointer params) as-is
            new_params = re.sub(r'br_word_t(\s+)(\w+)', r'uint8_t *restrict\1\2', params)
            # Also handle uintptr_t params
            new_params = re.sub(r'uintptr_t(\s+)(\w+)', r'uint8_t *restrict\1\2', new_params)
            # DON'T change uintptr_t* (return-by-pointer params)
            new_params = new_params.replace('uint8_t *restrict*', 'uintptr_t*')
            new_line = prefix + new_params + suffix
            new_lines.append(new_line)
        else:
            new_lines.append(line)
    lines = new_lines

    # Step 3: At call sites, cast uintptr_t expressions to uint8_t*
    # _br_load(expr) -> _br_load((const uint8_t*)(expr))
    # _br_store(expr, val) -> _br_store((uint8_t*)(expr), val)
    new_lines = []
    for line in lines:
        # Load calls: _br_load(expr+N) -> _br_load((const uint8_t*)(expr+N))
        # But skip if already typed (from the signature change)
        # The pattern: _br_load(WORD_EXPR) where WORD_EXPR is like "in0+0" or "out0+8"
        line = re.sub(
            r'_br_load\((\w+)\+(\d+)\)',
            r'_br_load((const uint8_t*)(\1+\2))',
            line)
        line = re.sub(
            r'_br_load\((\w+)\)',
            r'_br_load((const uint8_t*)\1)',
            line)
        # Store calls: _br_store(expr+N, val) -> _br_store((uint8_t*)(expr+N), val)
        line = re.sub(
            r'_br_store\((\w+)\+(\d+),',
            r'_br_store((uint8_t*)(\1+\2),',
            line)
        line = re.sub(
            r'_br_store\((\w+),',
            r'_br_store((uint8_t*)\1,',
            line)

        # Function calls: foo(expr, expr) -> foo((uint8_t*)expr, (uint8_t*)expr)
        # This is harder to do generically. For now, the function params are
        # uint8_t *restrict, and the arguments are uintptr_t locals.
        # GCC will implicitly convert uintptr_t to uint8_t* (with a warning).
        # To suppress warnings, we'd need explicit casts at every call site.
        # Let's add -Wno-int-conversion to the compile flags instead.

        new_lines.append(line)

    return '\n'.join(new_lines)

if __name__ == '__main__':
    print(transform(sys.stdin.read()))
