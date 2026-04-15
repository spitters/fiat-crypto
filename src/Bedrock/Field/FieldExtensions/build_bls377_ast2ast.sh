#!/usr/bin/env bash
# Build script for the BLS12-377 AST-to-AST Jasmin pipeline.
#
# Parallel to build_bn254_ast2ast.sh. Combines:
#   - bls377_jasmin_extracted.ml[i]  — [bls377_all_jasmin : jasmin_func list]
#     (from ExtractBLS377Jasmin.vo; reuse only the function-list surface)
#   - bridge_simple_v2.ml             — [to_jasmin_cmd] from JasminBridgeReal
#     (at fiat-crypto root; extracted in isolation to avoid the universe
#     conflict with bls12_377_prime)
#   - bls377_ast2ast_main.ml          — 30-line Obj.magic glue
#
# Usage:   ./build_bls377_ast2ast.sh
set -euo pipefail

FIAT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../../../" && pwd)"
RELDIR="src/Bedrock/Field/FieldExtensions"
EXTDIR="${FIAT_ROOT}/${RELDIR}"

eval "$(opam env --switch=rocq-native)"

echo "[1/3] Compile bls377_jasmin_extracted"
cd "${EXTDIR}"
rm -f bls377_jasmin_extracted.cmi bls377_jasmin_extracted.cmx \
      bls377_jasmin_extracted.o bls377_ast2ast_main.cmi \
      bls377_ast2ast_main.cmx bls377_ast2ast_main.o bls377_ast2ast_main
# ExtractBLS377Jasmin.vo does not emit an .mli, so ocamlopt will
# synthesize one from the .ml directly.
ocamlfind ocamlopt -c bls377_jasmin_extracted.ml

echo "[2/3] Recompile bridge_simple_v2 against jasmin.uint63-native"
rm -f "${FIAT_ROOT}/uint63.cmi" "${FIAT_ROOT}/uint63.cmx" "${FIAT_ROOT}/uint63.o" \
      "${FIAT_ROOT}/bridge_simple_v2.cmi" \
      "${FIAT_ROOT}/bridge_simple_v2.cmx" \
      "${FIAT_ROOT}/bridge_simple_v2.o"
(cd "${FIAT_ROOT}" && ocamlfind ocamlopt -package jasmin.uint63-native -c bridge_simple_v2.ml)

echo "[3/3] Compile + link bls377_ast2ast_main"
ocamlfind ocamlopt -package jasmin.uint63-native -I "${FIAT_ROOT}" -c bls377_ast2ast_main.ml
ocamlfind ocamlopt -package jasmin.uint63-native -linkpkg \
  "${FIAT_ROOT}/bridge_simple_v2.cmx" \
  bls377_jasmin_extracted.cmx \
  bls377_ast2ast_main.cmx \
  -o bls377_ast2ast_main

echo "built: ${EXTDIR}/bls377_ast2ast_main"
echo "(Runtime currently raises Uint63 AXIOM — see BRIDGE_SIMPLE_V2_README.md.)"
./bls377_ast2ast_main || true
