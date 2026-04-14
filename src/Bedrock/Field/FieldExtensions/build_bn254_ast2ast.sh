#!/usr/bin/env bash
# Build script for the BN254 AST-to-AST Jasmin pipeline.
#
# Combines:
#   - bn254_full_jasmin_extracted.ml[i]  — [bn254_full_jasmin : jasmin_func list]
#     (from ExtractBN254FullJasmin.vo; we reuse only the function-list surface,
#     not the deprecated text-path pretty-printer)
#   - bridge_simple_v2.ml                 — [to_jasmin_cmd] from JasminBridgeReal
#     (extracted in isolation at fiat-crypto/; avoids the universe conflict that
#     blocks importing JasminBridgeReal into any fiat-crypto file directly)
#   - bn254_ast2ast_main.ml               — 30-line Obj.magic glue
#
# Parallel to src/Bedrock/Field/FieldExtensions/ast2ast_main.ml for BLS12.
# Usage:   ./build_bn254_ast2ast.sh
set -euo pipefail

FIAT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../../../" && pwd)"
RELDIR="src/Bedrock/Field/FieldExtensions"
EXTDIR="${FIAT_ROOT}/${RELDIR}"

eval "$(opam env --switch=rocq-native)"

echo "[1/3] Compile bn254_full_jasmin_extracted"
cd "${EXTDIR}"
# Clean stale per-build artifacts
rm -f bn254_full_jasmin_extracted.cmi bn254_full_jasmin_extracted.cmx \
      bn254_full_jasmin_extracted.o bn254_ast2ast_main.cmi \
      bn254_ast2ast_main.cmx bn254_ast2ast_main.o bn254_ast2ast_main
ocamlfind ocamlopt -c bn254_full_jasmin_extracted.mli
ocamlfind ocamlopt -c bn254_full_jasmin_extracted.ml

echo "[2/3] Recompile bridge_simple_v2 against jasmin.uint63-native"
# bridge_simple_v2.ml lives at fiat-crypto root (extracted from
# JasminBridgeReal in isolation to avoid the universe conflict with
# coqutil). It uses [Uint63] from Coq's Stdlib, which extracts to
# OCaml's primitive int63; jasmin.uint63-native provides the matching
# runtime. We delete the stale local uint63.* stubs at fiat-crypto root
# so findlib unambiguously resolves to the jasmin package.
rm -f "${FIAT_ROOT}/uint63.cmi" "${FIAT_ROOT}/uint63.cmx" "${FIAT_ROOT}/uint63.o" \
      "${FIAT_ROOT}/bridge_simple_v2.cmi" \
      "${FIAT_ROOT}/bridge_simple_v2.cmx" \
      "${FIAT_ROOT}/bridge_simple_v2.o"
(cd "${FIAT_ROOT}" && ocamlfind ocamlopt -package jasmin.uint63-native -c bridge_simple_v2.ml)

echo "[3/3] Compile + link bn254_ast2ast_main"
ocamlfind ocamlopt -package jasmin.uint63-native -I "${FIAT_ROOT}" -c bn254_ast2ast_main.ml
ocamlfind ocamlopt -package jasmin.uint63-native -linkpkg \
  "${FIAT_ROOT}/bridge_simple_v2.cmx" \
  bn254_full_jasmin_extracted.cmx \
  bn254_ast2ast_main.cmx \
  -o bn254_ast2ast_main

echo "built: ${EXTDIR}/bn254_ast2ast_main"
echo "(Note: running it currently raises 'AXIOM TO BE REALIZED Uint63.lsl' —"
echo " same as the BLS12 ast2ast_main reference. bridge_simple_v2.ml has 8"
echo " unrealized Coq axioms (5 Uint63 ops + int_to_ident + int_to_funname)"
echo " that need Extract Constant directives in the upstream extraction."
echo " The compile-time wiring is verified end-to-end; runtime is pending.)"
./bn254_ast2ast_main || true
