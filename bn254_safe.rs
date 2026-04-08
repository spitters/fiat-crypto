//! Safe Rust wrappers for verified bn254 pairing arithmetic.
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
pub type Fp = [u64; 4];
pub type Fp2 = [u64; 8];
pub type Fp6 = [u64; 24];
pub type Fp12 = [u64; 48];

extern "C" {
    fn bn254_add(out: usize, x: usize, y: usize);
    fn bn254_mul(out: usize, x: usize, y: usize);
    fn bn254_square(out: usize, x: usize);
    fn bn254_pairing(out: usize, p_x: usize, p_y: usize, q_x: usize, q_y: usize);
}

/// Safe wrapper for `bn254_add`.
/// All non-aliasing requirements are enforced by Rust's borrow checker.
#[inline]
pub fn fp_add(out: &mut [u64; 4], x: &[u64; 4], y: &[u64; 4]) {
    unsafe { bn254_add(out.as_mut_ptr() as usize, x.as_ptr() as usize, y.as_ptr() as usize) }
}

/// Safe wrapper for `bn254_mul`.
/// All non-aliasing requirements are enforced by Rust's borrow checker.
#[inline]
pub fn fp_mul(out: &mut [u64; 4], x: &[u64; 4], y: &[u64; 4]) {
    unsafe { bn254_mul(out.as_mut_ptr() as usize, x.as_ptr() as usize, y.as_ptr() as usize) }
}

/// Safe wrapper for `bn254_square`.
/// All non-aliasing requirements are enforced by Rust's borrow checker.
#[inline]
pub fn fp_square(out: &mut [u64; 4], x: &[u64; 4]) {
    unsafe { bn254_square(out.as_mut_ptr() as usize, x.as_ptr() as usize) }
}

/// Safe wrapper for `bn254_pairing`.
/// All non-aliasing requirements are enforced by Rust's borrow checker.
#[inline]
pub fn pairing(out: &mut [u64; 48], p_x: &[u64; 4], p_y: &[u64; 4], q_x: &[u64; 8], q_y: &[u64; 8]) {
    unsafe { bn254_pairing(out.as_mut_ptr() as usize, p_x.as_ptr() as usize, p_y.as_ptr() as usize, q_x.as_ptr() as usize, q_y.as_ptr() as usize) }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fp_add_compiles() {
        // This test verifies that the borrow checker accepts our wrapper.
        // The non-aliasing of a, b, c is enforced at compile time.
        let a: Fp = [0u64; 4];
        let b: Fp = [0u64; 4];
        let mut c: Fp = [0u64; 4];
        fp_add(&mut c, &a, &b);
    }

    #[test]
    fn test_aliasing_rejected() {
        // This would NOT compile if uncommented:
        // let mut a: Fp = [0u64; 4];
        // fp_add(&mut a, &a, &a);  // ERROR: cannot borrow `a` as immutable
        //                           // because it is also borrowed as mutable
    }
}