#!/usr/bin/env python3
"""Inline tower wrapper functions into higher-level BLS24-509 functions.

This script reads the generated C code and inlines tower-level wrapper
functions (Fp2_*, Fp4_*, Fp8_*) into target functions (Fp24_mul, Fp24_square,
Fp24_inv), eliminating function call overhead and enabling the compiler to
optimize stack allocation across the flattened body.

Two modes:
  --light (default): Only inline cheap wrappers (add/sub/opp/copy/mul_xi/
    mul_by_nr/mul_by_v/mul_by_w). Minimal code expansion (~36% more lines).
  --full: Also inline mul/square at each tower level. Larger code expansion
    (~3.3x more lines) but flattens the entire computation into Fp-level calls.

IMPORTANT: The Fp base operations (bls24_509_mul, bls24_509_square,
bls24_509_add, bls24_509_sub, bls24_509_opp, bls24_509_felem_copy) are NEVER
inlined. Each contains 1500+ variables and inlining them would cause massive
register pressure, hurting performance.

Correctness: Verified to produce identical numerical results to the original
code for Fp8_mul, Fp24_mul, and Fp24_square with non-trivial test vectors.

Usage:
  python3 apply_inline.py bls24_509_pairing.c > output.c
  python3 apply_inline.py --full bls24_509_pairing.c > output.c
  python3 apply_inline.py --full --strip-zero-init bls24_509_pairing.c > output.c
"""

import sys
import re
from collections import OrderedDict

# ---------------------------------------------------------------------------
# Functions that should be inlined (tower wrappers only)
# ---------------------------------------------------------------------------

# INLINE_FULL: inline everything recursively (mul/sqr + add/sub/etc.)
INLINE_FULL = {
    # Fp2 level
    'bls24_Fp2_felem_copy',
    'bls24_Fp2_opp',
    'bls24_Fp2_add',
    'bls24_Fp2_sub',
    'bls24_Fp2_mul',
    'bls24_Fp2_square',
    'bls24_Fp2_mul_by_nr',
    'bls24_Fp2_mul_xi',
    # Fp4 level
    'bls24_Fp4_felem_copy',
    'bls24_Fp4_opp',
    'bls24_Fp4_add',
    'bls24_Fp4_sub',
    'bls24_Fp4_mul',
    'bls24_Fp4_square',
    'bls24_Fp4_mul_by_v',
    # Fp8 level
    'bls24_Fp8_felem_copy',
    'bls24_Fp8_opp',
    'bls24_Fp8_add',
    'bls24_Fp8_sub',
    'bls24_Fp8_mul',
    'bls24_Fp8_square',
    'bls24_Fp8_mul_by_w',
}

# INLINE_LIGHT: only inline cheap wrappers (add/sub/opp/copy/mul_xi/etc.)
# NOT mul/square (too much code expansion)
INLINE_LIGHT = {
    # Fp2 level
    'bls24_Fp2_felem_copy',
    'bls24_Fp2_opp',
    'bls24_Fp2_add',
    'bls24_Fp2_sub',
    'bls24_Fp2_mul_by_nr',
    'bls24_Fp2_mul_xi',
    # Fp4 level
    'bls24_Fp4_felem_copy',
    'bls24_Fp4_opp',
    'bls24_Fp4_add',
    'bls24_Fp4_sub',
    'bls24_Fp4_mul_by_v',
    # Fp8 level
    'bls24_Fp8_felem_copy',
    'bls24_Fp8_opp',
    'bls24_Fp8_add',
    'bls24_Fp8_sub',
    'bls24_Fp8_mul_by_w',
}

# Default: use light inlining (configurable via --full flag)
INLINE_FNS = INLINE_LIGHT

# Functions whose bodies we want to flatten (inline callees into).
# Only inline WITHIN tower mul/square operations, NOT into callers like
# miller_loop or final_exp -- those would cause too much code bloat and
# i-cache pressure.
TARGET_FNS = {
    'bls24_Fp4_mul',
    'bls24_Fp4_square',
    'bls24_Fp4_mul_by_v',
    'bls24_Fp8_mul',
    'bls24_Fp8_square',
    'bls24_Fp8_mul_by_w',
    'bls24_Fp24_mul',
    'bls24_Fp24_square',
    'bls24_Fp24_inv',
}

# Functions NOT to inline (Fp base operations)
KEEP_AS_CALL = {
    'bls24_509_add',
    'bls24_509_sub',
    'bls24_509_mul',
    'bls24_509_square',
    'bls24_509_opp',
    'bls24_509_felem_copy',
    'bls24_509_from_word',
    'bls24_509_select_znz',
    'bls24_509_zero',
    'bls24_509_one',
    'bls24_509_inv',
    # Tower ops we don't inline
    'bls24_Fp2_inv',
    'bls24_Fp4_inv',
    'bls24_Fp8_inv',
    'bls24_Fp2_select_znz',
    'bls24_Fp4_select_znz',
    'bls24_Fp8_select_znz',
    'bls24_Fp2_zero',
    'bls24_Fp2_one',
    'bls24_Fp4_zero',
    'bls24_Fp4_one',
    'bls24_Fp8_zero',
    'bls24_Fp8_one',
    'bls24_Fp24_zero',
    'bls24_Fp24_one',
    'bls24_Fp4_mul_fp',
}


def parse_functions(text):
    """Parse C file into list of (name, params, body_text, full_text) and non-function chunks."""
    lines = text.split('\n')
    func_def_re = re.compile(
        r'^(?:static\s+)?void\s+(\w+)\s*\(([^)]*)\)\s*\{')

    chunks = []  # list of ('text', content) or ('func', name, params, body_lines, full_text)
    i = 0
    text_buf = []

    while i < len(lines):
        m = func_def_re.match(lines[i])
        if m:
            if text_buf:
                chunks.append(('text', '\n'.join(text_buf)))
                text_buf = []
            fname = m.group(1)
            params_str = m.group(2)
            fn_lines = [lines[i]]
            i += 1
            depth = 1
            while i < len(lines) and depth > 0:
                depth += lines[i].count('{') - lines[i].count('}')
                fn_lines.append(lines[i])
                i += 1
            # Parse parameters
            params = []
            for p in params_str.split(','):
                p = p.strip()
                if p:
                    # Extract the parameter name (last word)
                    parts = p.split()
                    params.append(parts[-1])
            # Body is everything between the first { and last }
            # First line has the {, last line has the }
            body_lines = fn_lines[1:-1]  # exclude def line and closing }
            chunks.append(('func', fname, params, body_lines, '\n'.join(fn_lines)))
        else:
            text_buf.append(lines[i])
            i += 1

    if text_buf:
        chunks.append(('text', '\n'.join(text_buf)))

    return chunks


class InlineContext:
    """Manages variable naming during inlining."""

    def __init__(self):
        self.counter = 0
        self.stackallocs = []  # list of (var_name, size_str) to emit at top
        self.assignments = []  # list of "var = expr;" assignments

    def fresh_prefix(self):
        self.counter += 1
        return f'_il{self.counter}_'

    def add_stackalloc(self, var_name, size_str):
        self.stackallocs.append((var_name, size_str))

    def add_assignment(self, var_name, expr):
        self.assignments.append((var_name, expr))


def simplify_expr(expr):
    """Simplify pointer arithmetic expressions like ((out+128)+64) -> (out+192)."""
    # Recursively simplify (base+N)+M -> (base+(N+M))
    # Pattern: (EXPR+NUM)+NUM or EXPR+NUM+NUM
    changed = True
    while changed:
        changed = False
        # Match (expr+N)+M
        m = re.match(r'^\((.+)\+(\d+)\)\+(\d+)$', expr.strip())
        if m:
            inner = m.group(1)
            n1 = int(m.group(2))
            n2 = int(m.group(3))
            expr = f'({inner}+{n1+n2})'
            changed = True
            continue
        # Match (expr+0xN)+M or (expr+0xN)+0xM
        m = re.match(r'^\((.+)\+(0x[0-9a-fA-F]+)\)\+(0x[0-9a-fA-F]+|\d+)$', expr.strip())
        if m:
            inner = m.group(1)
            n1 = int(m.group(2), 0)
            n2 = int(m.group(3), 0)
            total = n1 + n2
            expr = f'({inner}+{total})'
            changed = True
            continue
        # Match (expr+N)+0xM
        m = re.match(r'^\((.+)\+(\d+)\)\+(0x[0-9a-fA-F]+)$', expr.strip())
        if m:
            inner = m.group(1)
            n1 = int(m.group(2))
            n2 = int(m.group(3), 0)
            total = n1 + n2
            expr = f'({inner}+{total})'
            changed = True
            continue
    return expr


def substitute_expr(expr, subst_map):
    """Apply substitution map to an expression, then simplify.

    subst_map maps parameter names to their replacement expressions.
    Handles arbitrary nesting of pointer arithmetic:
      base          -> subst[base]
      base+offset   -> (subst[base]+offset)
      (expr+N)      -> (subst_applied_expr+N)
      (expr+N)+M    -> simplified
    """
    expr = expr.strip()

    # Strip outer parens if they wrap the whole expression
    if expr.startswith('(') and expr.endswith(')'):
        # Check if the parens actually wrap everything (not just part)
        depth = 0
        is_wrapper = True
        for i, ch in enumerate(expr):
            if ch == '(':
                depth += 1
            elif ch == ')':
                depth -= 1
            if depth == 0 and i < len(expr) - 1:
                is_wrapper = False
                break
        if is_wrapper:
            inner = substitute_expr(expr[1:-1], subst_map)
            # Don't double-wrap if inner is already parenthesized
            if inner.startswith('(') and inner.endswith(')'):
                return inner
            # If inner is a simple identifier, no parens needed
            if re.match(r'^\w+$', inner):
                return inner
            return f'({inner})'

    # Direct match
    if expr in subst_map:
        return subst_map[expr]

    # Pattern: base+offset (where base is a simple identifier)
    m = re.match(r'^(\w+)\+(.+)$', expr)
    if m and m.group(1) in subst_map:
        base_replacement = subst_map[m.group(1)]
        offset = m.group(2)
        result = f'({base_replacement}+{offset})'
        return simplify_expr(result)

    # Pattern: (complex_expr)+offset
    m = re.match(r'^(\(.+\))\+(.+)$', expr)
    if m:
        inner = substitute_expr(m.group(1), subst_map)
        offset = m.group(2)
        result = f'({inner}+{offset})'
        return simplify_expr(result)

    # Pattern: base+offset where base has + in it (e.g., "inx+128+64")
    # Split at first +
    plus_idx = expr.find('+')
    if plus_idx > 0:
        base = expr[:plus_idx]
        offset = expr[plus_idx+1:]
        if base in subst_map:
            base_replacement = subst_map[base]
            result = f'({base_replacement}+{offset})'
            return simplify_expr(result)

    return expr


def try_parse_call(line_s):
    """Parse a function call statement, handling nested parentheses.

    Returns (func_name, args_string) or None if not a function call.
    Handles patterns like:
      bls24_509_add(out+128, inx, iny);
      bls24_509_add((out+128+64), (inx+64), (iny+64));
    """
    # Match: identifier( ... );
    m = re.match(r'^(\w+)\(', line_s)
    if not m:
        return None
    func_name = m.group(1)
    rest = line_s[m.end():]

    # Find the matching closing paren, handling nesting
    depth = 1
    i = 0
    while i < len(rest) and depth > 0:
        if rest[i] == '(':
            depth += 1
        elif rest[i] == ')':
            depth -= 1
        i += 1

    if depth != 0:
        return None

    # rest[0:i-1] is the args string, rest[i:] should be ";"
    args_str = rest[:i-1]
    remainder = rest[i:].strip()
    if remainder != ';':
        return None

    return (func_name, args_str)


def simultaneous_subst(text, subst_map):
    """Apply all substitutions simultaneously to avoid chained replacements.

    Unlike sequential re.sub calls, this finds all word-boundary matches
    and replaces them in one pass, so 'out' -> 'v0' doesn't then cause
    'v0' -> '_il13_v0' in the same substitution.
    """
    # Build a pattern matching any key in subst_map (word boundaries)
    if not subst_map:
        return text
    # Sort keys longest-first to avoid partial matches
    keys = sorted(subst_map.keys(), key=len, reverse=True)
    pattern = '|'.join(r'\b' + re.escape(k) + r'\b' for k in keys)
    def replacer(m):
        return subst_map[m.group(0)]
    return re.sub(pattern, replacer, text)


def inline_call(func_db, fname, args, ctx, indent='  ', depth=0):
    """Inline a function call, returning list of C code lines.

    func_db: dict mapping function name -> (params, body_lines)
    fname: function to inline
    args: list of argument expressions (as strings)
    ctx: InlineContext for managing fresh variable names
    indent: current indentation
    depth: recursion depth (for debugging)
    """
    if fname not in func_db:
        # Not in our database -- keep as external call
        args_str = ', '.join(args)
        return [f'{indent}{fname}({args_str});']

    if fname not in INLINE_FNS:
        # Explicitly keep as call
        args_str = ', '.join(args)
        return [f'{indent}{fname}({args_str});']

    params, body_lines = func_db[fname]

    if len(args) != len(params):
        # Mismatch -- keep as call (safety)
        args_str = ', '.join(args)
        return [f'{indent}{fname}({args_str});']

    # Build substitution map: param_name -> arg_expression
    subst = {}
    for param_name, arg_expr in zip(params, args):
        subst[param_name] = arg_expr

    prefix = ctx.fresh_prefix()
    result_lines = []
    result_lines.append(f'{indent}/* inlined: {fname}({", ".join(args)}) */')

    # Process each line of the body
    # Patterns we need to handle:
    # 1. "br_word_t v0, v1, v2;"  -- variable declarations
    # 2. "uint8_t _br_stackalloc_VAR[SIZE] = {0}; VAR = (br_word_t)&_br_stackalloc_VAR;"
    # 3. "FUNC(arg1, arg2, ...);"  -- function call
    # 4. "VAR = EXPR;"  -- assignment

    # First pass: collect all local variable names that need renaming
    local_vars = set()
    decl_re = re.compile(r'^\s*br_word_t\s+(.+);$')
    stackalloc_re = re.compile(
        r'^\s*uint8_t\s+(_br_stackalloc_(\w+))\[([^\]]+)\]\s*(?:=\s*\{0\})?\s*;\s*'
        r'(\w+)\s*=\s*\((?:br_word_t|uintptr_t)\)&\1;$')

    for line in body_lines:
        line_s = line.strip()
        dm = decl_re.match(line_s)
        if dm:
            for v in dm.group(1).split(','):
                v = v.strip()
                if v:
                    local_vars.add(v)
        sm = stackalloc_re.match(line_s)
        if sm:
            local_vars.add(sm.group(4))

    # Build local variable rename map
    local_rename = {}
    for v in local_vars:
        if v not in subst:  # Don't rename parameters
            local_rename[v] = prefix + v

    # Merge subst with local_rename for full substitution
    full_subst = {}
    full_subst.update(subst)
    full_subst.update(local_rename)

    # Second pass: emit transformed lines
    assign_re = re.compile(r'^\s*(\w+)\s*=\s*(.+);$')

    for line in body_lines:
        line_s = line.strip()

        # Skip empty lines
        if not line_s:
            continue

        # Skip inline comments
        if line_s.startswith('/*') and line_s.endswith('*/'):
            result_lines.append(f'{indent}{line_s}')
            continue

        # Variable declarations -- skip (we'll handle stackallocs directly)
        dm = decl_re.match(line_s)
        if dm:
            # Emit renamed declarations
            new_vars = []
            for v in dm.group(1).split(','):
                v = v.strip()
                if v and v in local_rename:
                    new_vars.append(local_rename[v])
            if new_vars:
                result_lines.append(f'{indent}br_word_t {", ".join(new_vars)};')
            continue

        # Stackalloc lines
        sm = stackalloc_re.match(line_s)
        if sm:
            alloc_name = sm.group(1)  # _br_stackalloc_VAR
            var_name = sm.group(4)
            size_str = sm.group(3)
            new_var = local_rename.get(var_name, var_name)
            new_alloc = f'_br_stackalloc_{new_var}'
            result_lines.append(
                f'{indent}uint8_t {new_alloc}[{size_str}] = {{0}}; '
                f'{new_var} = (br_word_t)&{new_alloc};')
            continue

        # Try to parse as function call: FUNC(args...);
        call_parsed = try_parse_call(line_s)
        if call_parsed:
            callee, args_str = call_parsed
            call_args = parse_call_args(args_str, full_subst)

            if callee in INLINE_FNS and callee in func_db and depth < 10:
                # Recursively inline
                inner = inline_call(func_db, callee, call_args, ctx,
                                    indent, depth + 1)
                result_lines.extend(inner)
            else:
                # Keep as external call
                new_args_str = ', '.join(call_args)
                result_lines.append(f'{indent}{callee}({new_args_str});')
            continue

        # Simple assignment: VAR = EXPR;
        am = assign_re.match(line_s)
        if am:
            var_name = am.group(1)
            expr = am.group(2)
            new_var = full_subst.get(var_name, var_name)
            new_expr = substitute_expr(expr, full_subst)
            result_lines.append(f'{indent}{new_var} = {new_expr};')
            continue

        # Anything else: try to substitute variables (simultaneous, not sequential)
        new_line = simultaneous_subst(line_s, full_subst)
        result_lines.append(f'{indent}{new_line}')

    return result_lines


def parse_call_args(args_str, subst_map):
    """Parse function call arguments and apply substitutions.

    Handles nested parentheses in arguments like (br_word_t)0.
    """
    args = []
    depth = 0
    current = ''
    for ch in args_str:
        if ch == '(' :
            depth += 1
            current += ch
        elif ch == ')':
            depth -= 1
            current += ch
        elif ch == ',' and depth == 0:
            args.append(current.strip())
            current = ''
        else:
            current += ch
    if current.strip():
        args.append(current.strip())

    # Apply substitutions to each argument
    result = []
    for arg in args:
        result.append(substitute_expr(arg, subst_map))
    return result


def transform_target_function(func_db, fname, params, body_lines, ctx):
    """Transform a target function by inlining all tower calls in its body."""
    result_lines = []
    indent = '  '

    stackalloc_re = re.compile(
        r'^\s*uint8_t\s+(_br_stackalloc_(\w+))\[([^\]]+)\]\s*(?:=\s*\{0\})?\s*;\s*'
        r'(\w+)\s*=\s*\((?:br_word_t|uintptr_t)\)&\1;$')
    decl_re = re.compile(r'^\s*br_word_t\s+(.+);$')
    assign_re = re.compile(r'^\s*(\w+)\s*=\s*(.+);$')

    # Identity substitution for top-level (no renaming needed)
    identity_subst = {}

    for line in body_lines:
        line_s = line.strip()

        # Pass through declarations and stackallocs as-is
        if decl_re.match(line_s) or stackalloc_re.match(line_s):
            result_lines.append(line)
            continue

        # Try to parse as function call
        call_parsed = try_parse_call(line_s)
        if call_parsed:
            callee, args_str = call_parsed
            call_args = parse_call_args(args_str, identity_subst)

            if callee in INLINE_FNS and callee in func_db:
                inlined = inline_call(func_db, callee, call_args, ctx, indent)
                result_lines.extend(inlined)
            else:
                result_lines.append(line)
            continue

        # Simple assignment (not a function call -- already checked above)
        am = assign_re.match(line_s)
        if am:
            result_lines.append(line)
            continue

        # Anything else: pass through
        result_lines.append(line)

    return result_lines


def build_func_db(chunks):
    """Build a dict mapping function names to (params, body_lines)."""
    db = OrderedDict()
    for chunk in chunks:
        if chunk[0] == 'func':
            _, fname, params, body_lines, _ = chunk
            db[fname] = (params, body_lines)
    return db


def optimize_output(lines, strip_zero_init=False):
    """Post-process inlined output to clean up redundant patterns.

    Optimizations:
    1. Remove self-assignments like "x = x;"
    2. Optionally strip = {0} from stackalloc arrays (they're always
       fully written before being read by Fp base ops)
    """
    result = []
    for line in lines:
        ls = line.strip()
        # Remove self-assignments
        m = re.match(r'^(\s*)(\w+)\s*=\s*(\w+);$', line)
        if m and m.group(2) == m.group(3):
            continue
        # Optionally strip zero-initialization from stackallocs
        if strip_zero_init:
            line = re.sub(r'(\[(?:64|128|0x[0-9a-fA-F]+|\d+)\])\s*=\s*\{0\}', r'\1', line)
        result.append(line)

    return result


def transform(text, strip_zero_init=False):
    """Main transformation: parse, inline, and reassemble."""
    chunks = parse_functions(text)
    func_db = build_func_db(chunks)

    ctx = InlineContext()

    # Process each chunk
    result_parts = []
    for chunk in chunks:
        if chunk[0] == 'text':
            result_parts.append(chunk[1])
        elif chunk[0] == 'func':
            _, fname, params, body_lines, full_text = chunk
            if fname in TARGET_FNS and fname in INLINE_FNS:
                # This function is both a target (inline its callees) AND
                # itself inlineable. We need to transform it.
                new_body = transform_target_function(func_db, fname, params,
                                                     body_lines, ctx)
                new_body = optimize_output(new_body, strip_zero_init)
                # Reconstruct function
                params_str = ', '.join(f'br_word_t {p}' for p in params)
                fn_text = f'void {fname}({params_str}) {{\n'
                fn_text += '\n'.join(new_body)
                fn_text += '\n}'
                result_parts.append(fn_text)
                # Update func_db with the inlined version so subsequent
                # inlining of this function uses the flattened body
                func_db[fname] = (params, new_body)
            elif fname in TARGET_FNS:
                # Only a target -- inline callees but this function itself
                # is not inlined into others
                new_body = transform_target_function(func_db, fname, params,
                                                     body_lines, ctx)
                new_body = optimize_output(new_body, strip_zero_init)
                params_str = ', '.join(f'br_word_t {p}' for p in params)
                fn_text = f'void {fname}({params_str}) {{\n'
                fn_text += '\n'.join(new_body)
                fn_text += '\n}'
                result_parts.append(fn_text)
            else:
                if strip_zero_init and fname in INLINE_FNS:
                    # Also strip zero-init from inlineable functions that
                    # are emitted as-is (they might be called directly)
                    new_lines = optimize_output(body_lines, strip_zero_init)
                    params_str = ', '.join(f'br_word_t {p}' for p in params)
                    fn_text = f'void {fname}({params_str}) {{\n'
                    fn_text += '\n'.join(new_lines)
                    fn_text += '\n}'
                    result_parts.append(fn_text)
                else:
                    result_parts.append(full_text)

    return '\n'.join(result_parts)


def main():
    global INLINE_FNS, TARGET_FNS

    import argparse
    parser = argparse.ArgumentParser(
        description='Inline tower wrapper functions in BLS24-509 C code')
    parser.add_argument('input', nargs='?', help='Input C file (stdin if omitted)')
    parser.add_argument('--full', action='store_true',
                        help='Full inlining (mul/sqr + add/sub/etc.)')
    parser.add_argument('--light', action='store_true', default=True,
                        help='Light inlining (add/sub/opp/copy only, default)')
    parser.add_argument('--strip-zero-init', action='store_true',
                        help='Remove = {0} from stackalloc arrays (unsafe but '
                             'correct for this codebase where arrays are always '
                             'fully written before read)')
    args = parser.parse_args()

    if args.full:
        INLINE_FNS = INLINE_FULL
        # With full inlining, also expand more target functions
        TARGET_FNS = {
            'bls24_Fp4_mul',
            'bls24_Fp4_square',
            'bls24_Fp4_mul_by_v',
            'bls24_Fp8_mul',
            'bls24_Fp8_square',
            'bls24_Fp8_mul_by_w',
            'bls24_Fp24_mul',
            'bls24_Fp24_square',
            'bls24_Fp24_inv',
        }
    else:
        INLINE_FNS = INLINE_LIGHT

    if args.input:
        with open(args.input) as f:
            text = f.read()
    else:
        text = sys.stdin.read()

    result = transform(text, strip_zero_init=args.strip_zero_init)
    print(result)


if __name__ == '__main__':
    main()
