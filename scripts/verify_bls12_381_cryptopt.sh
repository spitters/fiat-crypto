#!/usr/bin/env bash
# Verify CryptOpt-generated BLS12-381 assemblies via fiat-crypto's check_equivalence
#
# Verifies both:
#   - p-prime (Fp, base field): 6 limbs, mul + square
#   - q-prime (Fr, scalar field): 4 limbs, mul + square
#
# Usage: ./scripts/verify_bls12_381_cryptopt.sh
#        ./scripts/verify_bls12_381_cryptopt.sh <p_mul.asm> <p_sqr.asm> <q_mul.asm> <q_sqr.asm>
set -euo pipefail

WBW=./src/ExtractionOCaml/word_by_word_montgomery

P_PRIME='(-0xd201000000010000 -1)^2 * ((-0xd201000000010000)^4 - (-0xd201000000010000)^2 + 1)/3 + (-0xd201000000010000)'
Q_PRIME='(-0xd201000000010000)^4 -(-0xd201000000010000)^2 + 1'

CRYPTOPT_DIR="${CRYPTOPT_DIR:-/home/au528660/Claude/BLS/CryptOpt/generated/bls12}"

if [ ! -x "$WBW" ]; then
  echo "Building word_by_word_montgomery extraction..."
  make src/ExtractionOCaml/word_by_word_montgomery EXTERNAL_DEPENDENCIES=1
fi

P_MUL="${1:-$CRYPTOPT_DIR/fiat_bls12_381_p_mul/seed0000000046129964_ratio18433.asm}"
P_SQR="${2:-$CRYPTOPT_DIR/fiat_bls12_381_p_square/seed0000000271124530_ratio18886.asm}"
Q_MUL="${3:-$CRYPTOPT_DIR/fiat_bls12_381_q_mul/seed0000000575351056_ratio17105.asm}"
Q_SQR="${4:-$CRYPTOPT_DIR/fiat_bls12_381_q_square/seed0000000597540193_ratio20577.asm}"

verify() {
  local label="$1" curve="$2" prime="$3" method="$4" asm="$5"
  echo "=== $label: $asm ==="
  $WBW "$curve" 64 "$prime" "$method" \
    --hints-file "$asm" \
    -o /dev/null --output-asm /dev/null
  echo "  ✓ verified equivalent to fiat-crypto's $curve Montgomery $method"
}

verify "Fp mul"     bls12_381_p "$P_PRIME" mul    "$P_MUL"
verify "Fp square"  bls12_381_p "$P_PRIME" square "$P_SQR"
verify "Fr mul"     bls12_381_q "$Q_PRIME" mul    "$Q_MUL"
verify "Fr square"  bls12_381_q "$Q_PRIME" square "$Q_SQR"

echo
echo "All four BLS12-381 assemblies are formally verified equivalent to"
echo "fiat-crypto's Montgomery references for the base field (Fp) and the"
echo "scalar field (Fr)."
echo
echo "Trust footprint: fiat-crypto Montgomery proof + check_equivalence (verified Coq)."
