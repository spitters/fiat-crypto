#!/usr/bin/env python3
"""
Compute BN254 (alt_bn128, Ethereum) Frobenius constants for pairing.

Tower: Fp -> Fp2[u^2+1=0] -> Fp6[v^3 - xi = 0, xi=(9,1)] -> Fp12[w^2 - v = 0]

The Frobenius endomorphism pi: x -> x^p acts on the tower elements.
For Fp12 = Fp6[w]/(w^2-v), the key constants are powers of xi:

  gamma_{i,j} for the i-th Frobenius (pi^i) acting on coefficient j

Specifically for the standard BLS12/BN formulation:
  For Frobenius pi (x -> x^p):
    gamma_1_1 = xi^{(p-1)/6}        (for w coefficient in Fp12)
    gamma_1_2 = xi^{(p-1)/3}        (= gamma_1_1^2, for Fp6 v coefficient)
    gamma_1_3 = xi^{(p-1)/2}        (= gamma_1_1^3, for Fp6 v^2 coefficient)
    gamma_1_4 = xi^{2(p-1)/3}       (= gamma_1_1^4)
    gamma_1_5 = xi^{5(p-1)/6}       (= gamma_1_1^5)

  For Frobenius pi^2 (x -> x^{p^2}):
    gamma_2_1 = xi^{(p^2-1)/6}
    gamma_2_2 = xi^{(p^2-1)/3}
    gamma_2_3 = xi^{(p^2-1)/2}
    gamma_2_4 = xi^{2(p^2-1)/3}
    gamma_2_5 = xi^{5(p^2-1)/6}

  For Frobenius pi^3 (x -> x^{p^3}):
    gamma_3_1 = xi^{(p^3-1)/6}
    etc.

Montgomery form: mont(x) = (x * R) mod p, where R = 2^256.
Output: 4 x 64-bit limbs, little-endian.
"""


# BN254 parameters
p = 21888242871839275222246405745257275088696311157297823662689037894645226208583
# Verify p is prime (basic check)
assert pow(2, p - 1, p) == 1, "p fails Fermat test"

# Tower nonresidue xi = (9, 1) in Fp2
# Fp2 = Fp[u]/(u^2+1), so u^2 = -1
# beta = -1 (the Fp2 construction quadratic non-residue)

# Montgomery constant
R = 2**256

def to_mont(x):
    """Convert x to Montgomery form: (x * R) mod p."""
    return (x % p * R) % p

def to_limbs(x, n=4):
    """Split x into n 64-bit limbs, little-endian."""
    limbs = []
    for _ in range(n):
        limbs.append(x & ((1 << 64) - 1))
        x >>= 64
    assert x == 0, f"Value too large for {n} limbs"
    return limbs

def fmt_limbs(limbs):
    """Format limbs as hex strings."""
    return [f"0x{l:016x}" for l in limbs]

# Fp2 arithmetic: elements are (a, b) representing a + b*u where u^2 = -1
def fp2_add(x, y):
    return ((x[0] + y[0]) % p, (x[1] + y[1]) % p)

def fp2_sub(x, y):
    return ((x[0] - y[0]) % p, (x[1] - y[1]) % p)

def fp2_mul(x, y):
    """(a + bu)(c + du) = (ac - bd) + (ad + bc)u"""
    a, b = x
    c, d = y
    return ((a*c - b*d) % p, (a*d + b*c) % p)

def fp2_pow(base, exp):
    """Compute base^exp in Fp2 using square-and-multiply."""
    if exp == 0:
        return (1, 0)
    result = (1, 0)  # 1 in Fp2
    b = base
    while exp > 0:
        if exp & 1:
            result = fp2_mul(result, b)
        b = fp2_mul(b, b)
        exp >>= 1
    return result

def fp2_inv(x):
    """Inverse in Fp2: (a + bu)^{-1} = (a - bu)/(a^2 + b^2)."""
    a, b = x
    norm = (a*a + b*b) % p
    norm_inv = pow(norm, p - 2, p)
    return ((a * norm_inv) % p, ((-b) * norm_inv) % p)

def fp2_neg(x):
    return ((-x[0]) % p, (-x[1]) % p)

# xi = (9, 1) in Fp2
xi = (9, 1)

print("=" * 80)
print("BN254 Frobenius Constants")
print("=" * 80)
print(f"p = {p}")
print(f"p (hex) = 0x{p:064x}")
print(f"xi = {xi}")
print(f"R = 2^256")
print()

# Verify: xi is not a cube in Fp2 (needed for Fp6 construction)
# xi^((p^2-1)/3) should not be 1
test = fp2_pow(xi, (p*p - 1) // 3)
print(f"xi^((p^2-1)/3) = {test}")
assert test != (1, 0), "xi is a cube in Fp2, bad choice"
print()

# Compute all Frobenius constants
# For pi^i, the exponent base is (p^i - 1)

def compute_frobenius_set(i, label):
    """Compute gamma_{i,j} for j=1..5."""
    pi = p**i
    base_exp = pi - 1

    print(f"--- Frobenius pi^{i} ({label}) ---")
    print(f"p^{i} mod 6 = {pi % 6}")
    assert base_exp % 6 == 0, f"p^{i} - 1 not divisible by 6!"

    results = {}
    for j in range(1, 6):
        exp = (j * base_exp) // 6
        gamma = fp2_pow(xi, exp)
        results[j] = gamma

        re_mont = to_mont(gamma[0])
        im_mont = to_mont(gamma[1])
        re_limbs = fmt_limbs(to_limbs(re_mont))
        im_limbs = fmt_limbs(to_limbs(im_mont))

        print(f"  gamma_{i}_{j} = xi^{{{j}*(p^{i}-1)/6}} in Fp2:")
        print(f"    value = ({gamma[0]},")
        print(f"             {gamma[1]})")
        print(f"    Montgomery re: {re_limbs}")
        print(f"    Montgomery im: {im_limbs}")
        print()

    return results


# Compute for pi, pi^2, pi^3
frob1 = compute_frobenius_set(1, "x -> x^p")
frob2 = compute_frobenius_set(2, "x -> x^{p^2}")
frob3 = compute_frobenius_set(3, "x -> x^{p^3}")

# Verifications
print("=" * 80)
print("Verifications")
print("=" * 80)

# gamma_{1,1}^6 = xi^{p-1} = (Norm(xi))^{(p-1)/2} * something
# Actually xi^{p-1} = xi^p / xi, and for BN254 xi^p = conj(xi) = (9, -1)
# so xi^{p-1} = (9,-1)/(9,1) = (9,-1)*(9,-1)/(9^2+1^2) = (80,-18)/82 = (40,-9)/41
xi_p = fp2_pow(xi, p)
xi_conj = (xi[0], (-xi[1]) % p)
print(f"xi^p = {xi_p}")
print(f"conj(xi) = {xi_conj}")
assert xi_p == xi_conj, "xi^p != conj(xi) -- unexpected!"
print("PASS: xi^p = conj(xi) = (9, p-1)")

# Check gamma_{1,1}^6 = xi^{p-1}
g11_6 = fp2_pow(frob1[1], 6)
xi_pm1 = fp2_pow(xi, p - 1)
print(f"gamma_1_1^6 = {g11_6}")
print(f"xi^(p-1) = {xi_pm1}")
assert g11_6 == xi_pm1, "gamma_1_1^6 != xi^{p-1}"
print("PASS: gamma_1_1^6 = xi^{p-1}")

# Check gamma_{1,j} = gamma_{1,1}^j
for j in range(2, 6):
    g1j = frob1[j]
    g11_j = fp2_pow(frob1[1], j)
    assert g1j == g11_j, f"gamma_1_{j} != gamma_1_1^{j}"
print("PASS: gamma_1_j = gamma_1_1^j for j=2..5")

# Check gamma_{2,j} are in Fp (imaginary part = 0) since p^2-1 exponents
# make xi^{k(p^2-1)/6} land in Fp (because xi^{(p^2-1)} = 1)
for j in range(1, 6):
    assert frob2[j][1] == 0, f"gamma_2_{j} has nonzero imaginary part!"
print("PASS: All pi^2 constants are in Fp (imaginary part = 0)")

# gamma_{2,3} should be p-1 = -1 (since xi^{(p^2-1)/2} is a quadratic residue test)
assert frob2[3] == (p - 1, 0), f"gamma_2_3 != -1, got {frob2[3]}"
print("PASS: gamma_2_3 = -1")

print()

# ============================================================
# Output in format suitable for Rocq/bedrock2 embedding
# ============================================================
print("=" * 80)
print("Rocq/Bedrock2 Output (Montgomery form, 4x64-bit LE limbs)")
print("=" * 80)
print()

# For BN254 with 4 limbs, store functions use offsets 0, 8, 16, 24 for real
# and 32, 40, 48, 56 for imaginary

def print_rocq_fp2_const(name, comment, gamma, real_only=False):
    """Print a Frobenius constant in Rocq format."""
    re_mont = to_mont(gamma[0])
    im_mont = to_mont(gamma[1])
    re_limbs = to_limbs(re_mont)
    im_limbs = to_limbs(im_mont)

    is_real = (gamma[1] == 0)

    print(f"    (* {comment} *)")
    if is_real:
        print(f"    Definition {name} : function_t :=")
        print(f"      (\"{name}\",")
        print(f"       ([\"out\"], []:list String.string,")
        print(f"        store_fp2_real_only \"out\"")
        print(f"          0x{re_limbs[0]:016x} 0x{re_limbs[1]:016x}")
        print(f"          0x{re_limbs[2]:016x} 0x{re_limbs[3]:016x})).")
    else:
        print(f"    Definition {name} : function_t :=")
        print(f"      (\"{name}\",")
        print(f"       ([\"out\"], []:list String.string,")
        print(f"        store_fp2_full \"out\"")
        print(f"          0x{re_limbs[0]:016x} 0x{re_limbs[1]:016x}")
        print(f"          0x{re_limbs[2]:016x} 0x{re_limbs[3]:016x}")
        print(f"          0x{im_limbs[0]:016x} 0x{im_limbs[1]:016x}")
        print(f"          0x{im_limbs[2]:016x} 0x{im_limbs[3]:016x})).")
    print()


# The constants actually needed depend on the implementation.
# For final exponentiation easy part: need pi^2 constants (gamma_2_j)
# For final exponentiation hard part: need pi and pi^3 constants
#
# Standard naming (matching BLS12-381 convention):
#   gamma1     = xi^{(p-1)/3}      = gamma_{1,2}
#   gamma2     = xi^{2(p-1)/3}     = gamma_{1,4}
#   w_frob_c1  = xi^{(p-1)/6}      = gamma_{1,1}
#
#   gamma1_p2  = xi^{(p^2-1)/3}    = gamma_{2,2}
#   gamma2_p2  = xi^{2(p^2-1)/3}   = gamma_{2,4}
#   w_frob_p2_c1 = xi^{(p^2-1)/6}  = gamma_{2,1}
#
#   w_frob_p3_c1 = xi^{(p^3-1)/6}  = gamma_{3,1}

print("(* ============================================================== *)")
print("(* Frobenius p^2 constant loaders for BN254                       *)")
print("(* Values are in Montgomery form (R = 2^256), 4x64-bit LE limbs  *)")
print("(* ============================================================== *)")
print()

print_rocq_fp2_const("bn254_load_gamma1_p2",
                      "gamma1_p2 = xi^{(p^2-1)/3}",
                      frob2[2])

print_rocq_fp2_const("bn254_load_gamma2_p2",
                      "gamma2_p2 = xi^{2(p^2-1)/3}",
                      frob2[4])

print_rocq_fp2_const("bn254_load_w_frob_p2_c1",
                      "w_frob_p2_c1 = xi^{(p^2-1)/6}",
                      frob2[1])

print()
print("(* ============================================================== *)")
print("(* Frobenius p constant loaders for BN254                         *)")
print("(* ============================================================== *)")
print()

print_rocq_fp2_const("bn254_load_gamma1",
                      "gamma1 = xi^{(p-1)/3}",
                      frob1[2])

print_rocq_fp2_const("bn254_load_gamma2",
                      "gamma2 = xi^{2(p-1)/3}",
                      frob1[4])

print_rocq_fp2_const("bn254_load_w_frob_c1",
                      "w_frob_c1 = xi^{(p-1)/6}",
                      frob1[1])

print()
print("(* ============================================================== *)")
print("(* Frobenius p^3 constant loaders for BN254                       *)")
print("(* ============================================================== *)")
print()

print_rocq_fp2_const("bn254_load_w_frob_p3_c1",
                      "w_frob_p3_c1 = xi^{(p^3-1)/6}",
                      frob3[1])

# Also output gamma_{3,2..5} for completeness
print_rocq_fp2_const("bn254_load_gamma1_p3",
                      "gamma1_p3 = xi^{(p^3-1)/3}",
                      frob3[2])

print_rocq_fp2_const("bn254_load_gamma2_p3",
                      "gamma2_p3 = xi^{2(p^3-1)/3}",
                      frob3[4])

print()
print("=" * 80)
print("Raw values (non-Montgomery) for cross-checking with gnark-crypto")
print("=" * 80)
print()

def print_raw(name, gamma):
    print(f"{name}:")
    print(f"  re = {gamma[0]}")
    print(f"  im = {gamma[1]}")
    print(f"  re (hex) = 0x{gamma[0]:064x}")
    print(f"  im (hex) = 0x{gamma[1]:064x}")
    print()

print("--- pi constants ---")
print_raw("gamma_{1,1} = xi^{(p-1)/6}", frob1[1])
print_raw("gamma_{1,2} = xi^{(p-1)/3}", frob1[2])
print_raw("gamma_{1,3} = xi^{(p-1)/2}", frob1[3])
print_raw("gamma_{1,4} = xi^{2(p-1)/3}", frob1[4])
print_raw("gamma_{1,5} = xi^{5(p-1)/6}", frob1[5])

print("--- pi^2 constants ---")
print_raw("gamma_{2,1} = xi^{(p^2-1)/6}", frob2[1])
print_raw("gamma_{2,2} = xi^{(p^2-1)/3}", frob2[2])
print_raw("gamma_{2,3} = xi^{(p^2-1)/2}", frob2[3])
print_raw("gamma_{2,4} = xi^{2(p^2-1)/3}", frob2[4])
print_raw("gamma_{2,5} = xi^{5(p^2-1)/6}", frob2[5])

print("--- pi^3 constants ---")
print_raw("gamma_{3,1} = xi^{(p^3-1)/6}", frob3[1])
print_raw("gamma_{3,2} = xi^{(p^3-1)/3}", frob3[2])
print_raw("gamma_{3,3} = xi^{(p^3-1)/2}", frob3[3])
print_raw("gamma_{3,4} = xi^{2(p^3-1)/3}", frob3[4])
print_raw("gamma_{3,5} = xi^{5(p^3-1)/6}", frob3[5])

# Cross-check with known gnark-crypto values for BN254
# gnark-crypto uses the same tower but stores gamma values differently
# Let's verify a few well-known ones
print()
print("=" * 80)
print("Additional cross-checks")
print("=" * 80)

# The p^2 Frobenius constants should satisfy:
# gamma_{2,2}^3 = 1 (cube root of unity)
g22_cubed = fp2_pow(frob2[2], 3)
print(f"gamma_2_2^3 = {g22_cubed}")
assert g22_cubed == (1, 0), "gamma_2_2 is not a cube root of unity!"
print("PASS: gamma_2_2^3 = 1 (cube root of unity)")

# gamma_{2,1}^6 = 1 (6th root of unity)
g21_6 = fp2_pow(frob2[1], 6)
print(f"gamma_2_1^6 = {g21_6}")
assert g21_6 == (1, 0), "gamma_2_1 is not a 6th root of unity!"
print("PASS: gamma_2_1^6 = 1 (6th root of unity)")

# gamma_{2,1}^2 = gamma_{2,2}
g21_sq = fp2_mul(frob2[1], frob2[1])
assert g21_sq == frob2[2], "gamma_{2,1}^2 != gamma_{2,2}"
print("PASS: gamma_2_1^2 = gamma_2_2")

# Output store helpers for 4-limb BN254
print()
print("=" * 80)
print("Helper definitions for BN254 (4x64-bit limb store functions)")
print("=" * 80)
print()
print("""    (* Helper: store an Fp2 constant = (real, 0) where real is 4 limbs *)
    Local Definition store_fp2_real_only (v : string) (l0 l1 l2 l3 : Z) :=
      cmd_seq_list [
        cmd.store access_size.word (expr.var v) (expr.literal l0);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 8)) (expr.literal l1);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 16)) (expr.literal l2);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 24)) (expr.literal l3);
        (* Imaginary part = 0 *)
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 32)) (expr.literal 0);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 40)) (expr.literal 0);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 48)) (expr.literal 0);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 56)) (expr.literal 0)
      ].

    Local Definition store_fp2_full (v : string)
      (r0 r1 r2 r3 i0 i1 i2 i3 : Z) :=
      cmd_seq_list [
        cmd.store access_size.word (expr.var v) (expr.literal r0);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 8)) (expr.literal r1);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 16)) (expr.literal r2);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 24)) (expr.literal r3);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 32)) (expr.literal i0);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 40)) (expr.literal i1);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 48)) (expr.literal i2);
        cmd.store access_size.word
          (expr.op bopname.add (expr.var v) (expr.literal 56)) (expr.literal i3)
      ].""")
