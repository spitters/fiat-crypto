#!/usr/bin/env bash
# Build script for the BLS12-381 → Jasmin extraction pipeline.
#
# Steps:
#   1. Build ExtractBLS12Jasmin.vo (runs Coq's monolithic Extraction
#      of the [vm_compute]d [bls12_all_jasmin] / [bls12_optimized_jasmin]
#      and [pp_module]).
#   2. Compile [bls12_jasmin_extracted.ml] + [bls12_jasmin_main.ml].
#   3. Link [bls12_jasmin_main] which writes [.jazz] output.
#
# Usage:
#   ./build_bls12_jasmin.sh                    # build only
#   ./build_bls12_jasmin.sh out.jazz           # build + emit unflattened
#   ./build_bls12_jasmin.sh out.jazz flat      # build + emit flattened
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../../../" && pwd)"
EXTDIR="${REPO_ROOT}/src/Bedrock/Field/FieldExtensions"

cd "${REPO_ROOT}"

echo "[1/3] make ExtractBLS12Jasmin.vo"
eval "$(opam env --switch=rocq-native)"
export ROCQPATH="${HOME}/.opam/rocq-native/lib/coq/user-contrib"
make EXTERNAL_DEPENDENCIES=1 \
  src/Bedrock/Field/FieldExtensions/ExtractBLS12Jasmin.vo

echo "[2/3] compile bls12_jasmin_extracted + bls12_jasmin_main"
cd "${EXTDIR}"
# Clean stale artifacts from a previous build (object files only —
# never delete .ml/.mli, those are committed).
rm -f bls12_jasmin_extracted.cmi bls12_jasmin_extracted.cmx \
      bls12_jasmin_extracted.o bls12_jasmin_main.cmi \
      bls12_jasmin_main.cmx bls12_jasmin_main.o bls12_jasmin_main
ocamlfind ocamlopt -c bls12_jasmin_extracted.mli
ocamlfind ocamlopt -c bls12_jasmin_extracted.ml
ocamlfind ocamlopt -c bls12_jasmin_main.ml

echo "[3/3] link bls12_jasmin_main"
ocamlfind ocamlopt bls12_jasmin_extracted.cmx bls12_jasmin_main.cmx \
  -o bls12_jasmin_main

echo "built: ${EXTDIR}/bls12_jasmin_main"

if [ $# -ge 1 ]; then
  out="$1"; shift
  flag=""
  if [ $# -ge 1 ] && [ "$1" = "flat" ]; then flag="--flatten"; fi
  ./bls12_jasmin_main "${out}" ${flag}
fi
