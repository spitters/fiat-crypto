#!/usr/bin/env python3
"""Post-process bedrock2-generated C to use restrict-qualified pointer aliases.

For each static function, adds restrict pointer aliases for all uintptr_t
parameters, then #defines the parameter names to cast through the restrict
pointers. This gives GCC alias information to eliminate redundant copies.

Usage: python3 optimize_c.py < input.c > output.c
"""
import sys
import re

def process(text):
    lines = text.split('\n')
    result = []
    i = 0

    # Pattern: "static void fname(uintptr_t p1, uintptr_t p2, ...) {"
    # or "static uintptr_t fname(..."
    # The opening brace may be on the same line or is part of the params line
    func_start = re.compile(
        r'^static\s+(?:void|uintptr_t)\s+(\w+)\s*\(([^)]*)\)\s*\{')

    skip_fns = {'_br2_load', '_br2_store'}

    while i < len(lines):
        line = lines[i]
        m = func_start.match(line)

        if m and m.group(1) not in skip_fns:
            fname = m.group(1)
            params_str = m.group(2)

            # Parse pointer-sized integer parameters (uintptr_t or br_word_t)
            params = []
            for p in params_str.split(','):
                p = p.strip()
                if (p.startswith('uintptr_t ') or p.startswith('br_word_t ')) and '*' not in p:
                    params.append(p.split()[-1])

            # Emit the function header as-is
            result.append(line)
            i += 1

            if not params:
                continue

            # Look for the local variable declaration (first line after {)
            # It looks like: "  uintptr_t x, y, z;"
            local_decls = []
            while i < len(lines):
                stripped = lines[i].strip()
                if stripped.startswith('uintptr_t ') and stripped.endswith(';'):
                    local_decls.append(lines[i])
                    i += 1
                elif stripped.startswith('uint8_t _br') and 'stackalloc' in stripped:
                    # stackalloc line — emit as-is and continue looking
                    local_decls.append(lines[i])
                    i += 1
                else:
                    break

            # Emit local declarations
            for ld in local_decls:
                result.append(ld)

            # Emit restrict pointer aliases + #defines
            for pname in params:
                result.append(f'  uint8_t *restrict _rp_{pname} = (uint8_t*){pname};')
            for pname in params:
                result.append(f'  #define {pname} ((uintptr_t)_rp_{pname})')

            # Now emit the rest of the function body, tracking brace depth
            depth = 1  # we're inside the opening {
            while i < len(lines) and depth > 0:
                l = lines[i]
                depth += l.count('{') - l.count('}')
                if depth == 0:
                    # Closing brace — emit #undefs before it
                    for pname in params:
                        result.append(f'  #undef {pname}')
                    result.append(l)
                else:
                    result.append(l)
                i += 1
        else:
            result.append(line)
            i += 1

    return '\n'.join(result)

if __name__ == '__main__':
    print(process(sys.stdin.read()))
