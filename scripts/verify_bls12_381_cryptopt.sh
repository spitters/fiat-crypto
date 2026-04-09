#!/usr/bin/env bash
# Verify CryptOpt-generated BLS12-381 assembly via fiat-crypto's check_equivalence
#
# Usage: ./scripts/verify_bls12_381_cryptopt.sh <mul.asm> <square.asm>
#
# The .asm files must use only general-purpose registers (no xmm spilling),
# since fiat-crypto's check_equivalence doesn't yet support xmm operands.
# Pure-scalar CryptOpt outputs are in:
#   CryptOpt/generated/bls12/fiat_bls12_381_p_mul/seed*.asm
#   CryptOpt/generated/bls12/fiat_bls12_381_p_square/seed*.asm
set -euo pipefail

WBW=./src/ExtractionOCaml/word_by_word_montgomery
PRIME='(-0xd201000000010000 -1)^2 * ((-0xd201000000010000)^4 - (-0xd201000000010000)^2 + 1)/3 + (-0xd201000000010000)'

if [ ! -x "$WBW" ]; then
  echo "Building word_by_word_montgomery extraction..."
  make src/ExtractionOCaml/word_by_word_montgomery EXTERNAL_DEPENDENCIES=1
fi

MUL_ASM="${1:-/home/au528660/Claude/BLS/CryptOpt/generated/bls12/fiat_bls12_381_p_mul/seed0000000046129964_ratio18433.asm}"
SQR_ASM="${2:-/home/au528660/Claude/BLS/CryptOpt/generated/bls12/fiat_bls12_381_p_square/seed0000000271124530_ratio18886.asm}"

echo "=== Verifying mul: $MUL_ASM ==="
$WBW 'bls12_381_p' 64 "$PRIME" mul \
  --hints-file "$MUL_ASM" \
  -o /dev/null --output-asm /dev/null
echo "  ✓ verified equivalent to fiat-crypto's bls12_381_p Montgomery mul"

echo "=== Verifying square: $SQR_ASM ==="
$WBW 'bls12_381_p' 64 "$PRIME" square \
  --hints-file "$SQR_ASM" \
  -o /dev/null --output-asm /dev/null
echo "  ✓ verified equivalent to fiat-crypto's bls12_381_p Montgomery square"

echo
echo "Both assemblies are formally verified equivalent to fiat-crypto's reference."
echo "Trust footprint: fiat-crypto Montgomery proof + check_equivalence (verified Coq)."
