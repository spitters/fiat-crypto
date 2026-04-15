#!/usr/bin/env bash
# Build script for bn254_compile_direct — verified AST-to-AST x86-64 emitter.
set -euo pipefail

FIAT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../../../" && pwd)"
RELDIR="src/Bedrock/Field/FieldExtensions"
EXTDIR="${FIAT_ROOT}/${RELDIR}"

eval "$(opam env --switch=rocq-native)"

if [ -z "$(ocamlfind query jasmin.jasmin 2>/dev/null || true)" ]; then
  echo "ERROR: jasmin.jasmin not found. Install jasmin in rocq-native switch."
  exit 1
fi

PACKAGES="jasmin.uint63-native,jasmin.jasmin"
cd "${EXTDIR}"

rm -f bn254_full_jasmin_extracted.cmi bn254_full_jasmin_extracted.cmx \
      bn254_full_jasmin_extracted.o bn254_compile_direct.cmi \
      bn254_compile_direct.cmx bn254_compile_direct.o bn254_compile_direct \
      "${FIAT_ROOT}/uint63.cmi" "${FIAT_ROOT}/uint63.cmx" "${FIAT_ROOT}/uint63.o" \
      "${FIAT_ROOT}/bridge_simple_v2.cmi" \
      "${FIAT_ROOT}/bridge_simple_v2.cmx" "${FIAT_ROOT}/bridge_simple_v2.o"

echo "[1/4] Compile bn254_full_jasmin_extracted"
ocamlfind ocamlopt -c bn254_full_jasmin_extracted.mli
ocamlfind ocamlopt -c bn254_full_jasmin_extracted.ml

echo "[2/4] Compile bridge_simple_v2"
(cd "${FIAT_ROOT}" && ocamlfind ocamlopt -package jasmin.uint63-native -c bridge_simple_v2.ml)

echo "[3/4] Compile bn254_compile_direct"
ocamlfind ocamlopt -package "${PACKAGES}" -I "${FIAT_ROOT}" -c bn254_compile_direct.ml

echo "[4/4] Link"
ocamlfind ocamlopt -package "${PACKAGES}" -linkpkg \
  "${FIAT_ROOT}/bridge_simple_v2.cmx" \
  bn254_full_jasmin_extracted.cmx \
  bn254_compile_direct.cmx \
  -o bn254_compile_direct

echo "built: ${EXTDIR}/bn254_compile_direct"
echo "(Runtime blocked on Uint63 axioms — see BRIDGE_SIMPLE_V2_README.md.)"
