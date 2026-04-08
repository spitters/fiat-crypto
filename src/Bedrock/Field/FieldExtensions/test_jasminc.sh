#!/usr/bin/env bash
# End-to-end smoke test: extract BLS12-381 functions through ToJasmin
# and run jasminc on the simplest ones (no [stackalloc]) to confirm
# the bedrock2 -> Coq AST -> OCaml extraction -> ToJasmin -> jasminc
# -> x86-64 .s -> .o pipeline runs all the way through.
#
# Functions like [bls12_Fp2_mul_xi] that need a stack temp do NOT
# round-trip cleanly yet because Jasmin's type system rejects
# passing a [stack u64[N]] where a [reg u64] is expected — a
# bedrock2-style raw-pointer model needs an additional Jasmin-level
# pointer-extraction pass on the AST.  See README for the workaround.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../../../" && pwd)"
EXTDIR="${REPO_ROOT}/src/Bedrock/Field/FieldExtensions"
OUT="${BLS12_JASMIN_OUT:-/tmp/bls12_pairing.jazz}"

eval "$(opam env --switch=rocq-native)"

if [ ! -f "${OUT}" ]; then
  echo "[smoke] generating ${OUT}"
  "${EXTDIR}/build_bls12_jasmin.sh" "${OUT}"
fi

WORK=$(mktemp -d)
trap 'rm -rf "${WORK}"' EXIT

# Functions that have no stack temporaries — pure load/op/store
# bodies that should round-trip cleanly through jasminc.  We slice
# each function out of the bundle and feed it individually.
GOOD_FNS=(bls12_felem_copy)

passed=0
failed=0
for fn in "${GOOD_FNS[@]}"; do
  awk -v fn="${fn}" '
    $0 ~ "^export fn " fn "\\(" { p=1 }
    p { print }
    p && $0 == "}" { exit }
  ' "${OUT}" > "${WORK}/${fn}.jazz"
  if [ ! -s "${WORK}/${fn}.jazz" ]; then
    echo "[smoke] FAIL ${fn}: not found in ${OUT}"
    failed=$((failed+1))
    continue
  fi
  if jasminc "${WORK}/${fn}.jazz" -o "${WORK}/${fn}.s" 2>"${WORK}/${fn}.err"; then
    if as "${WORK}/${fn}.s" -o "${WORK}/${fn}.o" 2>>"${WORK}/${fn}.err"; then
      sym=$(objdump -t "${WORK}/${fn}.o" | awk -v fn="${fn}" '$NF == fn {print fn}')
      if [ "${sym}" = "${fn}" ]; then
        echo "[smoke] OK ${fn}: jasminc + as + symbol present"
        passed=$((passed+1))
        continue
      fi
    fi
  fi
  echo "[smoke] FAIL ${fn}:"
  cat "${WORK}/${fn}.err" | sed 's/^/    /'
  failed=$((failed+1))
done

echo "[smoke] ${passed} passed, ${failed} failed"
[ "${failed}" -eq 0 ]
