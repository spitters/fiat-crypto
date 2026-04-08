#!/usr/bin/env python3
"""Generate safe Rust wrappers for bedrock2-extracted C functions.

Reads a spec description (manually derived from fnspec! in Rocq) and
emits a Rust module with:
  1. Type aliases (Fp, Fp2, Fp6, Fp12) mapping to fixed-size u64 arrays
  2. extern "C" declarations for the raw bedrock2 functions
  3. Safe public wrappers using &/&mut references

The key insight: bedrock2's separation logic specs tell us:
  - Which args are read-only vs mutated (presence unchanged in postcondition)
  - Buffer sizes (from FElem_Fp, FElem_Fp2, etc.)
  - Non-aliasing requirements (from ⋆)
Rust's borrow checker enforces these statically.
"""

import json
import sys

# ============================================================
# Spec descriptions (derived from fnspec! in Rocq)
# ============================================================

# Each entry: (rust_name, c_name, params)
# param: (name, type, mode)
#   type: "Fp", "Fp2", "Fp6", "Fp12"
#   mode: "out" (mutated), "in" (read-only)

CURVES = {
    "bls12_381": {
        "prefix": "bls12",
        "limbs": 6,  # 381-bit prime, 6x64
        "types": {
            "Fp":   {"limbs": 6,  "bytes": 48},
            "Fp2":  {"limbs": 12, "bytes": 96},
            "Fp6":  {"limbs": 36, "bytes": 288},
            "Fp12": {"limbs": 72, "bytes": 576},
        },
        "functions": [
            # Fp-level
            ("fp_add",    "bls12_add",    [("out", "Fp", "out"), ("x", "Fp", "in"), ("y", "Fp", "in")]),
            ("fp_sub",    "bls12_sub",    [("out", "Fp", "out"), ("x", "Fp", "in"), ("y", "Fp", "in")]),
            ("fp_mul",    "bls12_mul",    [("out", "Fp", "out"), ("x", "Fp", "in"), ("y", "Fp", "in")]),
            ("fp_square", "bls12_square", [("out", "Fp", "out"), ("x", "Fp", "in")]),
            # Fp2-level
            ("fp2_add",    "bls12_Fp2_add",    [("out", "Fp2", "out"), ("x", "Fp2", "in"), ("y", "Fp2", "in")]),
            ("fp2_sub",    "bls12_Fp2_sub",    [("out", "Fp2", "out"), ("x", "Fp2", "in"), ("y", "Fp2", "in")]),
            ("fp2_mul",    "bls12_Fp2_mul",    [("out", "Fp2", "out"), ("x", "Fp2", "in"), ("y", "Fp2", "in")]),
            ("fp2_square", "bls12_Fp2_square", [("out", "Fp2", "out"), ("x", "Fp2", "in")]),
            ("fp2_inv",    "bls12_Fp2_inv",    [("out", "Fp2", "out"), ("x", "Fp2", "in")]),
            # Fp12-level
            ("fp12_mul",    "bls12_Fp12_mul",    [("out", "Fp12", "out"), ("x", "Fp12", "in"), ("y", "Fp12", "in")]),
            ("fp12_square", "bls12_Fp12_square", [("out", "Fp12", "out"), ("x", "Fp12", "in")]),
            # Pairing
            ("pairing", "bls12_pairing", [
                ("out", "Fp12", "out"),
                ("p_x", "Fp",   "in"),
                ("p_y", "Fp",   "in"),
                ("q_x", "Fp2",  "in"),
                ("q_y", "Fp2",  "in"),
            ]),
            # Miller loop
            ("miller_loop", "bls12_miller_loop", [
                ("out", "Fp12", "out"),
                ("p_x", "Fp",   "in"),
                ("p_y", "Fp",   "in"),
                ("q_x", "Fp2",  "in"),
                ("q_y", "Fp2",  "in"),
            ]),
        ],
    },
    "bls12_377": {
        "prefix": "bls377",
        "limbs": 6,
        "types": {
            "Fp":   {"limbs": 6,  "bytes": 48},
            "Fp2":  {"limbs": 12, "bytes": 96},
            "Fp6":  {"limbs": 36, "bytes": 288},
            "Fp12": {"limbs": 72, "bytes": 576},
        },
        "functions": [
            ("fp_add",    "bls377_add",    [("out", "Fp", "out"), ("x", "Fp", "in"), ("y", "Fp", "in")]),
            ("fp_mul",    "bls377_mul",    [("out", "Fp", "out"), ("x", "Fp", "in"), ("y", "Fp", "in")]),
            ("fp_square", "bls377_square", [("out", "Fp", "out"), ("x", "Fp", "in")]),
            ("pairing", "bls377_pairing_dsd", [
                ("out", "Fp12", "out"),
                ("p_x", "Fp",   "in"),
                ("p_y", "Fp",   "in"),
                ("q_x", "Fp2",  "in"),
                ("q_y", "Fp2",  "in"),
            ]),
        ],
    },
    "bn254": {
        "prefix": "bn254",
        "limbs": 4,  # 254-bit prime, 4x64
        "types": {
            "Fp":   {"limbs": 4,  "bytes": 32},
            "Fp2":  {"limbs": 8,  "bytes": 64},
            "Fp6":  {"limbs": 24, "bytes": 192},
            "Fp12": {"limbs": 48, "bytes": 384},
        },
        "functions": [
            ("fp_add",    "bn254_add",    [("out", "Fp", "out"), ("x", "Fp", "in"), ("y", "Fp", "in")]),
            ("fp_mul",    "bn254_mul",    [("out", "Fp", "out"), ("x", "Fp", "in"), ("y", "Fp", "in")]),
            ("fp_square", "bn254_square", [("out", "Fp", "out"), ("x", "Fp", "in")]),
            ("pairing", "bn254_pairing", [
                ("out", "Fp12", "out"),
                ("p_x", "Fp",   "in"),
                ("p_y", "Fp",   "in"),
                ("q_x", "Fp2",  "in"),
                ("q_y", "Fp2",  "in"),
            ]),
        ],
    },
}


def rust_type(ty: str, mode: str, types: dict) -> str:
    """Map (type, mode) to Rust reference type."""
    limbs = types[ty]["limbs"]
    inner = f"[u64; {limbs}]"
    if mode == "out":
        return f"&mut {inner}"
    else:
        return f"&{inner}"


def gen_extern_decl(c_name: str, params: list, types: dict) -> str:
    """Generate extern "C" declaration."""
    args = []
    for name, ty, mode in params:
        args.append(f"{name}: usize")
    return f'    fn {c_name}({", ".join(args)});'


def gen_safe_wrapper(rust_name: str, c_name: str, params: list, types: dict) -> str:
    """Generate safe Rust wrapper function."""
    # Build safe parameter list
    safe_params = []
    for name, ty, mode in params:
        safe_params.append(f"{name}: {rust_type(ty, mode, types)}")

    # Build unsafe call with pointer casts
    call_args = []
    for name, ty, mode in params:
        if mode == "out":
            call_args.append(f"{name}.as_mut_ptr() as usize")
        else:
            call_args.append(f"{name}.as_ptr() as usize")

    lines = []
    lines.append(f"/// Safe wrapper for `{c_name}`.")
    lines.append(f"/// All non-aliasing requirements are enforced by Rust's borrow checker.")
    lines.append(f"#[inline]")
    lines.append(f"pub fn {rust_name}({', '.join(safe_params)}) {{")
    lines.append(f"    unsafe {{ {c_name}({', '.join(call_args)}) }}")
    lines.append(f"}}")
    return "\n".join(lines)


def gen_module(curve_name: str, spec: dict) -> str:
    """Generate a complete Rust module for a curve."""
    types = spec["types"]
    prefix = spec["prefix"]

    lines = []
    lines.append(f"//! Safe Rust wrappers for verified {curve_name} pairing arithmetic.")
    lines.append(f"//!")
    lines.append(f"//! Generated from bedrock2 separation logic specifications.")
    lines.append(f"//! All functions are verified for functional correctness and memory safety.")
    lines.append(f"//! Non-aliasing invariants are enforced by Rust's borrow checker.")
    lines.append(f"//!")
    lines.append(f"//! # Safety")
    lines.append(f"//! The `unsafe` block in each wrapper calls the verified C/Jasmin function.")
    lines.append(f"//! Safety is guaranteed by the bedrock2 separation logic proof,")
    lines.append(f"//! which establishes that the function respects the pointer layout")
    lines.append(f"//! encoded in the Rust reference types.")
    lines.append(f"")

    # Type aliases
    lines.append(f"// Field element types (Montgomery form, little-endian limbs)")
    for ty_name, ty_info in types.items():
        lines.append(f"pub type {ty_name} = [u64; {ty_info['limbs']}];")
    lines.append(f"")

    # Extern declarations
    lines.append(f"extern \"C\" {{")
    for rust_name, c_name, params in spec["functions"]:
        lines.append(gen_extern_decl(c_name, params, types))
    lines.append(f"}}")
    lines.append(f"")

    # Safe wrappers
    for rust_name, c_name, params in spec["functions"]:
        lines.append(gen_safe_wrapper(rust_name, c_name, params, types))
        lines.append(f"")

    # Test module
    lines.append(f"#[cfg(test)]")
    lines.append(f"mod tests {{")
    lines.append(f"    use super::*;")
    lines.append(f"")
    lines.append(f"    #[test]")
    lines.append(f"    fn test_fp_add_compiles() {{")
    lines.append(f"        // This test verifies that the borrow checker accepts our wrapper.")
    lines.append(f"        // The non-aliasing of a, b, c is enforced at compile time.")
    limbs = types["Fp"]["limbs"]
    lines.append(f"        let a: Fp = [0u64; {limbs}];")
    lines.append(f"        let b: Fp = [0u64; {limbs}];")
    lines.append(f"        let mut c: Fp = [0u64; {limbs}];")
    lines.append(f"        fp_add(&mut c, &a, &b);")
    lines.append(f"    }}")
    lines.append(f"")
    lines.append(f"    #[test]")
    lines.append(f"    fn test_aliasing_rejected() {{")
    lines.append(f"        // This would NOT compile if uncommented:")
    lines.append(f"        // let mut a: Fp = [0u64; {limbs}];")
    lines.append(f"        // fp_add(&mut a, &a, &a);  // ERROR: cannot borrow `a` as immutable")
    lines.append(f"        //                           // because it is also borrowed as mutable")
    lines.append(f"    }}")
    lines.append(f"}}")

    return "\n".join(lines)


def main():
    if len(sys.argv) > 1:
        curve = sys.argv[1]
    else:
        curve = "bls12_381"

    if curve == "all":
        for name, spec in CURVES.items():
            filename = f"{name}_safe.rs"
            with open(filename, "w") as f:
                f.write(gen_module(name, spec))
            print(f"Generated {filename}")
    elif curve in CURVES:
        print(gen_module(curve, CURVES[curve]))
    else:
        print(f"Unknown curve: {curve}. Available: {', '.join(CURVES.keys())}, all")
        sys.exit(1)


if __name__ == "__main__":
    main()
