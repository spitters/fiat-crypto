/* ======================================================================
   BLS24-509 tower field inversions: Fp2, Fp4, Fp8.

   These implement the norm-based inversion formula for quadratic extensions:
     inv(a + b*t) = (a * norm_inv) - (b * norm_inv) * t
   where norm = a^2 - nr * b^2  and  norm_inv = inv(norm) in the sub-field.

   Tower structure:
     Fp2 = Fp[u] / (u^2 + 1)        beta = -1    => norm = a^2 + b^2
     Fp4 = Fp2[x] / (x^2 - xi)      xi = 1+u     => norm = a^2 - xi*b^2
     Fp8 = Fp4[v] / (v^2 - v_nr)    v_nr = x      => norm = a^2 - v_nr*b^2

   Field element sizes (bytes):
     Fp = 64,  Fp2 = 128,  Fp4 = 256,  Fp8 = 512

   All functions use the bedrock2 br_word_t (uintptr_t) calling convention.
   ====================================================================== */

/* Forward declarations for functions defined in bench_bls24.c and extracted code */

/* Fp operations */
extern void bls24_509_inv(br_word_t out, br_word_t x);
extern void bls24_509_mul(br_word_t out, br_word_t in0, br_word_t in1);
extern void bls24_509_square(br_word_t out, br_word_t in0);
extern void bls24_509_add(br_word_t out, br_word_t in0, br_word_t in1);
extern void bls24_509_sub(br_word_t out, br_word_t in0, br_word_t in1);

/* Fp2 operations */
extern void bls24_Fp2_mul(br_word_t out, br_word_t inx, br_word_t iny);
extern void bls24_Fp2_square(br_word_t out, br_word_t x);
extern void bls24_Fp2_sub(br_word_t out, br_word_t inx, br_word_t iny);
extern void bls24_Fp2_opp(br_word_t out, br_word_t x);
extern void bls24_Fp2_mul_xi(br_word_t out, br_word_t x);
extern void bls24_Fp2_felem_copy(br_word_t out, br_word_t x);

/* Fp4 operations */
extern void bls24_Fp4_mul(br_word_t out, br_word_t inx, br_word_t iny);
extern void bls24_Fp4_square(br_word_t out, br_word_t x);
extern void bls24_Fp4_sub(br_word_t out, br_word_t inx, br_word_t iny);
extern void bls24_Fp4_opp(br_word_t out, br_word_t x);
extern void bls24_Fp4_mul_by_v(br_word_t out, br_word_t x);
extern void bls24_Fp4_felem_copy(br_word_t out, br_word_t x);

/* ======================================================================
   Fp2 inversion: inv(a + b*u) where u^2 = -1
   norm = a^2 + b^2  (since beta = -1, and -beta = +1)
   inv  = (a/norm) - (b/norm)*u
   ====================================================================== */
void bls24_Fp2_inv(br_word_t out, br_word_t x) {
    uint8_t _buf_a2[64]   = {0};  br_word_t a2   = (br_word_t)_buf_a2;
    uint8_t _buf_b2[64]   = {0};  br_word_t b2   = (br_word_t)_buf_b2;
    uint8_t _buf_norm[64] = {0};  br_word_t norm = (br_word_t)_buf_norm;
    uint8_t _buf_ninv[64] = {0};  br_word_t ninv = (br_word_t)_buf_ninv;

    /* a = x[0..63], b = x[64..127] */
    br_word_t xa = x;
    br_word_t xb = x + 64;

    /* norm = a^2 + b^2 */
    bls24_509_square(a2, xa);
    bls24_509_square(b2, xb);
    bls24_509_add(norm, a2, b2);

    /* ninv = inv(norm) in Fp */
    bls24_509_inv(ninv, norm);

    /* out.a = a * ninv,  out.b = -(b * ninv) */
    bls24_509_mul(out,      xa, ninv);
    bls24_509_mul(out + 64, xb, ninv);
    bls24_509_opp(out + 64, out + 64);
}

/* ======================================================================
   Fp4 inversion: inv(a + b*x) where x^2 = xi  (xi = 1+u in Fp2)
   norm = a^2 - xi * b^2
   inv  = (a * norm_inv) - (b * norm_inv) * x
   ====================================================================== */
void bls24_Fp4_inv(br_word_t out, br_word_t x) {
    uint8_t _buf_a2[128]    = {0};  br_word_t a2     = (br_word_t)_buf_a2;
    uint8_t _buf_xib2[128]  = {0};  br_word_t xib2   = (br_word_t)_buf_xib2;
    uint8_t _buf_norm[128]  = {0};  br_word_t norm   = (br_word_t)_buf_norm;
    uint8_t _buf_ninv[128]  = {0};  br_word_t ninv   = (br_word_t)_buf_ninv;
    uint8_t _buf_tmp[128]   = {0};  br_word_t tmp    = (br_word_t)_buf_tmp;

    /* a = x[0..127] (Fp2), b = x[128..255] (Fp2) */
    br_word_t xa = x;
    br_word_t xb = x + 128;

    /* norm = a^2 - xi * b^2 */
    bls24_Fp2_square(a2, xa);
    bls24_Fp2_square(xib2, xb);
    bls24_Fp2_mul_xi(xib2, xib2);   /* xib2 = xi * b^2 */
    bls24_Fp2_sub(norm, a2, xib2);

    /* ninv = inv(norm) in Fp2 */
    bls24_Fp2_inv(ninv, norm);

    /* out.a = a * ninv,  out.b = -(b * ninv) */
    bls24_Fp2_mul(out,       xa, ninv);
    bls24_Fp2_mul(out + 128, xb, ninv);
    bls24_Fp2_opp(out + 128, out + 128);
}

/* ======================================================================
   Fp8 inversion: inv(a + b*v) where v^2 = v_nr  (v_nr is the Fp4
   element corresponding to "x" in the tower, i.e., (0,1) in Fp4)
   norm = a^2 - v_nr * b^2
   inv  = (a * norm_inv) - (b * norm_inv) * v
   ====================================================================== */
void bls24_Fp8_inv(br_word_t out, br_word_t x) {
    uint8_t _buf_a2[256]    = {0};  br_word_t a2     = (br_word_t)_buf_a2;
    uint8_t _buf_vb2[256]   = {0};  br_word_t vb2    = (br_word_t)_buf_vb2;
    uint8_t _buf_norm[256]  = {0};  br_word_t norm   = (br_word_t)_buf_norm;
    uint8_t _buf_ninv[256]  = {0};  br_word_t ninv   = (br_word_t)_buf_ninv;

    /* a = x[0..255] (Fp4), b = x[256..511] (Fp4) */
    br_word_t xa = x;
    br_word_t xb = x + 256;

    /* norm = a^2 - v_nr * b^2 */
    bls24_Fp4_square(a2, xa);
    bls24_Fp4_square(vb2, xb);
    bls24_Fp4_mul_by_v(vb2, vb2);   /* vb2 = v_nr * b^2 */
    bls24_Fp4_sub(norm, a2, vb2);

    /* ninv = inv(norm) in Fp4 */
    bls24_Fp4_inv(ninv, norm);

    /* out.a = a * ninv,  out.b = -(b * ninv) */
    bls24_Fp4_mul(out,       xa, ninv);
    bls24_Fp4_mul(out + 256, xb, ninv);
    bls24_Fp4_opp(out + 256, out + 256);
}
