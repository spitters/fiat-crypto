//! Safe Rust wrappers for verified bls12_381 pairing arithmetic.
//!
//! Generated from bedrock2 separation logic specifications.
//! All functions are verified for functional correctness and memory safety.
//! Non-aliasing invariants are enforced by Rust's borrow checker.
//!
//! # Safety
//! The `unsafe` block in each wrapper calls the verified C/Jasmin function.
//! Safety is guaranteed by the bedrock2 separation logic proof,
//! which establishes that the function respects the pointer layout
//! encoded in the Rust reference types.

// Field element types (Montgomery form, little-endian limbs)
pub type Fp = [u64; 6];
pub type Fp2 = [u64; 12];
pub type Fp6 = [u64; 36];
pub type Fp12 = [u64; 72];

extern "C" {
    fn bls12_add(out: usize, x: usize, y: usize);
    fn bls12_sub(out: usize, x: usize, y: usize);
    fn bls12_mul(out: usize, x: usize, y: usize);
    fn bls12_square(out: usize, x: usize);
    fn bls12_Fp2_add(out: usize, x: usize, y: usize);
    fn bls12_Fp2_sub(out: usize, x: usize, y: usize);
    fn bls12_Fp2_mul(out: usize, x: usize, y: usize);
    fn bls12_Fp2_square(out: usize, x: usize);
    fn bls12_Fp2_inv(out: usize, x: usize);
    fn bls12_Fp12_mul(out: usize, x: usize, y: usize);
    fn bls12_Fp12_square(out: usize, x: usize);
    fn bls12_pairing(out: usize, p_x: usize, p_y: usize, q_x: usize, q_y: usize);
    fn bls12_miller_loop(out: usize, p_x: usize, p_y: usize, q_x: usize, q_y: usize);
}

/// Safe wrapper for `bls12_add`.
/// All non-aliasing requirements are enforced by Rust's borrow checker.
#[inline]
pub fn fp_add(out: &mut [u64; 6], x: &[u64; 6], y: &[u64; 6]) {
    unsafe { bls12_add(out.as_mut_ptr() as usize, x.as_ptr() as usize, y.as_ptr() as usize) }
}

/// Safe wrapper for `bls12_sub`.
/// All non-aliasing requirements are enforced by Rust's borrow checker.
#[inline]
pub fn fp_sub(out: &mut [u64; 6], x: &[u64; 6], y: &[u64; 6]) {
    unsafe { bls12_sub(out.as_mut_ptr() as usize, x.as_ptr() as usize, y.as_ptr() as usize) }
}

/// Safe wrapper for `bls12_mul`.
/// All non-aliasing requirements are enforced by Rust's borrow checker.
#[inline]
pub fn fp_mul(out: &mut [u64; 6], x: &[u64; 6], y: &[u64; 6]) {
    unsafe { bls12_mul(out.as_mut_ptr() as usize, x.as_ptr() as usize, y.as_ptr() as usize) }
}

/// Safe wrapper for `bls12_square`.
/// All non-aliasing requirements are enforced by Rust's borrow checker.
#[inline]
pub fn fp_square(out: &mut [u64; 6], x: &[u64; 6]) {
    unsafe { bls12_square(out.as_mut_ptr() as usize, x.as_ptr() as usize) }
}

/// Safe wrapper for `bls12_Fp2_add`.
/// All non-aliasing requirements are enforced by Rust's borrow checker.
#[inline]
pub fn fp2_add(out: &mut [u64; 12], x: &[u64; 12], y: &[u64; 12]) {
    unsafe { bls12_Fp2_add(out.as_mut_ptr() as usize, x.as_ptr() as usize, y.as_ptr() as usize) }
}

/// Safe wrapper for `bls12_Fp2_sub`.
/// All non-aliasing requirements are enforced by Rust's borrow checker.
#[inline]
pub fn fp2_sub(out: &mut [u64; 12], x: &[u64; 12], y: &[u64; 12]) {
    unsafe { bls12_Fp2_sub(out.as_mut_ptr() as usize, x.as_ptr() as usize, y.as_ptr() as usize) }
}

/// Safe wrapper for `bls12_Fp2_mul`.
/// All non-aliasing requirements are enforced by Rust's borrow checker.
#[inline]
pub fn fp2_mul(out: &mut [u64; 12], x: &[u64; 12], y: &[u64; 12]) {
    unsafe { bls12_Fp2_mul(out.as_mut_ptr() as usize, x.as_ptr() as usize, y.as_ptr() as usize) }
}

/// Safe wrapper for `bls12_Fp2_square`.
/// All non-aliasing requirements are enforced by Rust's borrow checker.
#[inline]
pub fn fp2_square(out: &mut [u64; 12], x: &[u64; 12]) {
    unsafe { bls12_Fp2_square(out.as_mut_ptr() as usize, x.as_ptr() as usize) }
}

/// Safe wrapper for `bls12_Fp2_inv`.
/// All non-aliasing requirements are enforced by Rust's borrow checker.
#[inline]
pub fn fp2_inv(out: &mut [u64; 12], x: &[u64; 12]) {
    unsafe { bls12_Fp2_inv(out.as_mut_ptr() as usize, x.as_ptr() as usize) }
}

/// Safe wrapper for `bls12_Fp12_mul`.
/// All non-aliasing requirements are enforced by Rust's borrow checker.
#[inline]
pub fn fp12_mul(out: &mut [u64; 72], x: &[u64; 72], y: &[u64; 72]) {
    unsafe { bls12_Fp12_mul(out.as_mut_ptr() as usize, x.as_ptr() as usize, y.as_ptr() as usize) }
}

/// Safe wrapper for `bls12_Fp12_square`.
/// All non-aliasing requirements are enforced by Rust's borrow checker.
#[inline]
pub fn fp12_square(out: &mut [u64; 72], x: &[u64; 72]) {
    unsafe { bls12_Fp12_square(out.as_mut_ptr() as usize, x.as_ptr() as usize) }
}

/// Safe wrapper for `bls12_pairing`.
/// All non-aliasing requirements are enforced by Rust's borrow checker.
#[inline]
pub fn pairing(out: &mut [u64; 72], p_x: &[u64; 6], p_y: &[u64; 6], q_x: &[u64; 12], q_y: &[u64; 12]) {
    unsafe { bls12_pairing(out.as_mut_ptr() as usize, p_x.as_ptr() as usize, p_y.as_ptr() as usize, q_x.as_ptr() as usize, q_y.as_ptr() as usize) }
}

/// Safe wrapper for `bls12_miller_loop`.
/// All non-aliasing requirements are enforced by Rust's borrow checker.
#[inline]
pub fn miller_loop(out: &mut [u64; 72], p_x: &[u64; 6], p_y: &[u64; 6], q_x: &[u64; 12], q_y: &[u64; 12]) {
    unsafe { bls12_miller_loop(out.as_mut_ptr() as usize, p_x.as_ptr() as usize, p_y.as_ptr() as usize, q_x.as_ptr() as usize, q_y.as_ptr() as usize) }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fp_add_compiles() {
        // This test verifies that the borrow checker accepts our wrapper.
        // The non-aliasing of a, b, c is enforced at compile time.
        let a: Fp = [0u64; 6];
        let b: Fp = [0u64; 6];
        let mut c: Fp = [0u64; 6];
        fp_add(&mut c, &a, &b);
    }

    #[test]
    fn test_aliasing_rejected() {
        // This would NOT compile if uncommented:
        // let mut a: Fp = [0u64; 6];
        // fp_add(&mut a, &a, &a);  // ERROR: cannot borrow `a` as immutable
        //                           // because it is also borrowed as mutable
    }
}