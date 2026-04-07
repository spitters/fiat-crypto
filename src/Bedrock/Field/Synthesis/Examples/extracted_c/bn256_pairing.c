     = "// Generated from Bedrock code. Avoid editing directly.
#include <stdint.h>
#include <string.h>
#include <assert.h>

#define BR_WORD_MAX UINTPTR_MAX
typedef uintptr_t br_word_t;
typedef intptr_t br_signed_t;

static_assert(sizeof(br_word_t) == sizeof(br_signed_t), ""signed size"");
static_assert(UINTPTR_MAX <= BR_WORD_MAX, ""pointer fits in int"");
static_assert(~(br_signed_t)0 == -(br_signed_t)1, ""two's complement"");

#if __STDC_VERSION__ >= 202311L && __has_include(<stdbit.h>)
  #include <stdbit.h>
  static_assert(__STDC_ENDIAN_NATIVE__ == __STDC_ENDIAN_LITTLE__, ""little-endian"");
#elif defined(__GNUC__) && defined(__BYTE_ORDER__) && defined(__ORDER_LITTLE_ENDIAN__)
  static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__, ""little-endian"");
#elif defined(_MSC_VER) && !defined(__clang__) &&                              \
    (defined(_M_IX86) || defined(_M_X64) || defined(_M_ARM) || defined(_M_ARM64))
  // these MSVC targets are little-endian
#else
  #error ""failed to confirm that target is little-endian""
#endif

// ""An object shall have its stored value accessed only ... a character type.""
static inline br_word_t _br_load1(br_word_t a) {
  return *((uint8_t *)a);
}

static inline br_word_t _br_load2(br_word_t a) {
  uint16_t r = 0;
  memcpy(&r, (void *)a, sizeof(r));
  return r;
}

static inline br_word_t _br_load4(br_word_t a) {
  uint32_t r = 0;
  memcpy(&r, (void *)a, sizeof(r));
  return r;
}

static inline br_word_t _br_load(br_word_t a) {
  br_word_t r = 0;
  memcpy(&r, (void *)a, sizeof(r));
  return r;
}

static inline void _br_store1(br_word_t a, uint8_t v) {
  *((uint8_t *)a) = v;
}

static inline void _br_store2(br_word_t a, uint16_t v) {
  memcpy((void *)a, &v, sizeof(v));
}

static inline void _br_store4(br_word_t a, uint32_t v) {
  memcpy((void *)a, &v, sizeof(v));
}

static inline void _br_store(br_word_t a, br_word_t v) {
  memcpy((void *)a, &v, sizeof(v));
}

static inline br_word_t _br_mulhuu(br_word_t a, br_word_t b) {
  #if BR_WORD_MAX == UINT32_MAX
	  return ((uint64_t)a * b) >> 32;
  #elif BR_WORD_MAX == UINT64_MAX && (defined(__GNUC__) || defined(__clang__))
    return ((unsigned __int128)a * b) >> 64;
  #elif defined(_M_X64)
    uint64_t hi;
    _umul128(a, b, &hi);
    return hi;
  #elif defined(_M_ARM64)
    return __umulh(a, b);
  #else
    // See full_mul.v
    br_word_t hh, lh, hl, low, second_halfword_w_oflow, n, ll, M;
    n = ((((0u-(br_word_t)0x1)>>27)&0x3f)+0x1)>>1;
    M = ((br_word_t)0x1<<n)-0x1;
    ll = (a&M)*(b&M);
    lh = (a&M)*(b>>n);
    hl = (a>>n)*(b&M);
    hh = (a>>n)*(b>>n);
    second_halfword_w_oflow = ((ll>>n)+(lh&M))+(hl&M);
    return ((hh+(lh>>n))+(hl>>n))+(second_halfword_w_oflow>>n);
  #endif
}

static inline br_word_t _br_divu(br_word_t a, br_word_t b) {
  if (!b) return -1;
  return a/b;
}

static inline br_word_t _br_remu(br_word_t a, br_word_t b) {
  if (!b) return a;
  return a%b;
}

static void bn256_sub(br_word_t out0, br_word_t in0, br_word_t in1);
static void bn256_mul(br_word_t out0, br_word_t in0, br_word_t in1);
static void bn256_square(br_word_t out0, br_word_t in0);
static void bn256_select_znz(br_word_t out0, br_word_t in0, br_word_t in1, br_word_t in2);
static void bn256_felem_copy(br_word_t out, br_word_t in);
static void bn256_Fp2_mul_xi(br_word_t out, br_word_t x);
static void bn256_Fp6_felem_copy(br_word_t out, br_word_t x);
static void bn256_Fp6_add(br_word_t out, br_word_t inx, br_word_t iny);
static void bn256_Fp6_sub(br_word_t out, br_word_t inx, br_word_t iny);
static void bn256_Fp6_opp(br_word_t out, br_word_t x);
static void bn256_Fp6_mul(br_word_t out, br_word_t inx, br_word_t iny);
static void bn256_Fp6_square(br_word_t out, br_word_t x);
static void bn256_Fp6_inv(br_word_t out, br_word_t x);
static void bn256_Fp6_add_nocopy(br_word_t out, br_word_t inx, br_word_t iny);
static void bn256_Fp6_sub_nocopy(br_word_t out, br_word_t inx, br_word_t iny);
static void bn256_Fp6_mul_by_v(br_word_t out, br_word_t x);
static void bn256_Fp12_felem_copy(br_word_t out, br_word_t x);
static void bn256_Fp12_add(br_word_t out, br_word_t inx, br_word_t iny);
static void bn256_Fp12_sub(br_word_t out, br_word_t inx, br_word_t iny);
static void bn256_Fp12_opp(br_word_t out, br_word_t x);
static void bn256_Fp12_conjugate(br_word_t out, br_word_t x);
static void bn256_Fp12_mul(br_word_t out, br_word_t inx, br_word_t iny);
static void bn256_Fp12_square(br_word_t out, br_word_t x);
static void bn256_Fp12_inv(br_word_t out, br_word_t x);
static void bn256_Fp12_add_nocopy(br_word_t out, br_word_t inx, br_word_t iny);
static void bn256_Fp12_sub_nocopy(br_word_t out, br_word_t inx, br_word_t iny);
static void bn256_Fp12_mul_nocopy(br_word_t out, br_word_t inx, br_word_t iny);
static void bn256_Fp2_conjugate(br_word_t out, br_word_t x);
static void bn256_Fp6_mul_fp2(br_word_t out, br_word_t x, br_word_t s);
static void bn256_Fp6_frobenius(br_word_t out, br_word_t x, br_word_t gamma1, br_word_t gamma2);
static void bn256_Fp6_frobenius_p2(br_word_t out, br_word_t x, br_word_t gamma1_p2, br_word_t gamma2_p2);
static void bn256_Fp12_frobenius(br_word_t out, br_word_t x, br_word_t gamma1, br_word_t gamma2, br_word_t w_frob_c1);
static void bn256_Fp12_frobenius_p2(br_word_t out, br_word_t x, br_word_t gamma1_p2, br_word_t gamma2_p2, br_word_t w_frob_p2_c1);
static void bn256_Fp12_frobenius_p3(br_word_t out, br_word_t x, br_word_t gamma1, br_word_t gamma2, br_word_t gamma1_p2, br_word_t gamma2_p2, br_word_t w_frob_c1, br_word_t w_frob_p2_c1);
static void bn256_Fp2_mul_fp(br_word_t out, br_word_t x, br_word_t s);
static void bn256_make_line(br_word_t out, br_word_t lam, br_word_t x_t, br_word_t y_t, br_word_t x_p, br_word_t y_p);
static void bn256_load_gamma1_p2(br_word_t out);
static void bn256_load_gamma2_p2(br_word_t out);
static void bn256_load_w_frob_p2_c1(br_word_t out);
static void bn256_load_gamma1(br_word_t out);
static void bn256_load_gamma2(br_word_t out);
static void bn256_load_w_frob_c1(br_word_t out);
static void bn256_Fp12_pow_u(br_word_t out, br_word_t base);
static void bn256_final_exp_hard_dsd(br_word_t out, br_word_t f);
static void bn256_final_exp_dsd(br_word_t out, br_word_t f, br_word_t gamma1_p2, br_word_t gamma2_p2, br_word_t w_frob_p2_c1);
static void bn256_miller_loop(br_word_t out, br_word_t p_x, br_word_t p_y, br_word_t q_x, br_word_t q_y);
static void bn256_pairing_dsd(br_word_t out, br_word_t p_x, br_word_t p_y, br_word_t q_x, br_word_t q_y);

void bn256_add(br_word_t out0, br_word_t in0, br_word_t in1) {
  br_word_t x4, x0, x9, x1, x5, x11, x2, x6, x13, x3, x7, x17, x19, x15, x21, x8, x24, x16, x25, x10, x27, x18, x28, x12, x30, x20, x31, x23, x14, x33, x22, x34, x26, x29, x32, x35, x36, x37, x38, x39;
  x0 = _br_load(in0+0);
  x1 = _br_load(in0+8);
  x2 = _br_load(in0+16);
  x3 = _br_load(in0+24);
  /*skip*/
  x4 = _br_load(in1+0);
  x5 = _br_load(in1+8);
  x6 = _br_load(in1+16);
  x7 = _br_load(in1+24);
  /*skip*/
  /*skip*/
  x8 = x0+x4;
  x9 = ((br_word_t)(x8<x0))+x1;
  x10 = x9+x5;
  x11 = (((br_word_t)(x9<x1))+((br_word_t)(x10<x5)))+x2;
  x12 = x11+x6;
  x13 = (((br_word_t)(x11<x2))+((br_word_t)(x12<x6)))+x3;
  x14 = x13+x7;
  x15 = ((br_word_t)(x13<x3))+((br_word_t)(x14<x7));
  x16 = x8-0x185cac6c5e089667;
  x17 = x10-0xee5b88d120b5b59e ;
  x18 = x17-((br_word_t)(x8<x16));
  x19 = x12-0xaa6fecb86184dc21;
  x20 = x19-(((br_word_t)(x10<x17))+((br_word_t)(x17<x18)));
  x21 = x14-0x8fb501e34aa387f9;
  x22 = x21-(((br_word_t)(x12<x19))+((br_word_t)(x19<x20)));
  x23 = (br_word_t)(x15<(x15-(((br_word_t)(x14<x21))+((br_word_t)(x21<x22)))));
  x24 = (0u-(br_word_t)1)+((br_word_t)(x23==(br_word_t)0));
  x25 = x24^0xffffffffffffffff;
  x26 = (x8&x24)|(x16&x25);
  x27 = (0u-(br_word_t)1)+((br_word_t)(x23==(br_word_t)0));
  x28 = x27^0xffffffffffffffff;
  x29 = (x10&x27)|(x18&x28);
  x30 = (0u-(br_word_t)1)+((br_word_t)(x23==(br_word_t)0));
  x31 = x30^0xffffffffffffffff;
  x32 = (x12&x30)|(x20&x31);
  x33 = (0u-(br_word_t)1)+((br_word_t)(x23==(br_word_t)0));
  x34 = x33^0xffffffffffffffff;
  x35 = (x14&x33)|(x22&x34);
  x36 = x26;
  x37 = x29;
  x38 = x32;
  x39 = x35;
  /*skip*/
  _br_store(out0+0, x36);
  _br_store(out0+8, x37);
  _br_store(out0+16, x38);
  _br_store(out0+24, x39);
  /*skip*/
}

static void bn256_sub(br_word_t out0, br_word_t in0, br_word_t in1) {
  br_word_t x4, x5, x0, x6, x1, x9, x7, x2, x11, x3, x13, x8, x17, x10, x19, x12, x14, x15, x16, x18, x20, x21, x22, x23, x24, x25;
  x0 = _br_load(in0+0);
  x1 = _br_load(in0+8);
  x2 = _br_load(in0+16);
  x3 = _br_load(in0+24);
  /*skip*/
  x4 = _br_load(in1+0);
  x5 = _br_load(in1+8);
  x6 = _br_load(in1+16);
  x7 = _br_load(in1+24);
  /*skip*/
  /*skip*/
  x8 = x0-x4;
  x9 = x1-x5;
  x10 = x9-((br_word_t)(x0<x8));
  x11 = x2-x6;
  x12 = x11-(((br_word_t)(x1<x9))+((br_word_t)(x9<x10)));
  x13 = x3-x7;
  x14 = x13-(((br_word_t)(x2<x11))+((br_word_t)(x11<x12)));
  x15 = (0u-(br_word_t)1)+((br_word_t)((((br_word_t)(x3<x13))+((br_word_t)(x13<x14)))==(br_word_t)0));
  x16 = x8+(x15&0x185cac6c5e089667);
  x17 = ((br_word_t)(x16<x8))+x10;
  x18 = x17+(x15&0xee5b88d120b5b59e );
  x19 = (((br_word_t)(x17<x10))+((br_word_t)(x18<(x15&0xee5b88d120b5b59e ))))+x12;
  x20 = x19+(x15&0xaa6fecb86184dc21);
  x21 = ((((br_word_t)(x19<x12))+((br_word_t)(x20<(x15&0xaa6fecb86184dc21))))+x14)+(x15&0x8fb501e34aa387f9);
  x22 = x16;
  x23 = x18;
  x24 = x20;
  x25 = x21;
  /*skip*/
  _br_store(out0+0, x22);
  _br_store(out0+8, x23);
  _br_store(out0+16, x24);
  _br_store(out0+24, x25);
  /*skip*/
}

static void bn256_mul(br_word_t out0, br_word_t in0, br_word_t in1) {
  br_word_t x1, x2, x3, x0, x11, x16, x19, x21, x17, x22, x14, x23, x25, x26, x15, x27, x12, x28, x30, x31, x13, x33, x38, x41, x43, x39, x44, x36, x45, x47, x48, x37, x49, x34, x50, x52, x53, x35, x40, x55, x18, x56, x20, x57, x42, x58, x60, x61, x24, x62, x46, x63, x65, x66, x29, x67, x51, x68, x70, x71, x32, x72, x54, x73, x75, x8, x81, x84, x86, x82, x87, x79, x88, x90, x91, x80, x92, x77, x93, x95, x96, x78, x83, x59, x99, x64, x100, x85, x101, x103, x104, x69, x105, x89, x106, x108, x109, x74, x110, x94, x111, x113, x114, x76, x115, x97, x116, x118, x120, x125, x128, x130, x126, x131, x123, x132, x134, x135, x124, x136, x121, x137, x139, x140, x122, x127, x142, x98, x143, x102, x144, x129, x145, x147, x148, x107, x149, x133, x150, x152, x153, x112, x154, x138, x155, x157, x158, x117, x159, x141, x160, x162, x163, x119, x9, x169, x172, x174, x170, x175, x167, x176, x178, x179, x168, x180, x165, x181, x183, x184, x166, x171, x146, x187, x151, x188, x173, x189, x191, x192, x156, x193, x177, x194, x196, x197, x161, x198, x182, x199, x201, x202, x164, x203, x185, x204, x206, x208, x213, x216, x218, x214, x219, x211, x220, x222, x223, x212, x224, x209, x225, x227, x228, x210, x215, x230, x186, x231, x190, x232, x217, x233, x235, x236, x195, x237, x221, x238, x240, x241, x200, x242, x226, x243, x245, x246, x205, x247, x229, x248, x250, x251, x207, x7, x6, x5, x10, x4, x257, x260, x262, x258, x263, x255, x264, x266, x267, x256, x268, x253, x269, x271, x272, x254, x259, x234, x275, x239, x276, x261, x277, x279, x280, x244, x281, x265, x282, x284, x285, x249, x286, x270, x287, x289, x290, x252, x291, x273, x292, x294, x296, x301, x304, x306, x302, x307, x299, x308, x310, x311, x300, x312, x297, x313, x315, x316, x298, x303, x318, x274, x319, x278, x320, x305, x321, x323, x324, x283, x325, x309, x326, x328, x329, x288, x330, x314, x331, x333, x334, x293, x335, x317, x336, x338, x339, x295, x342, x343, x344, x346, x347, x348, x349, x351, x352, x353, x354, x356, x357, x340, x358, x322, x360, x341, x361, x327, x363, x345, x364, x332, x366, x350, x367, x359, x337, x369, x355, x370, x362, x365, x368, x371, x372, x373, x374, x375;
  x0 = _br_load(in0+0);
  x1 = _br_load(in0+8);
  x2 = _br_load(in0+16);
  x3 = _br_load(in0+24);
  /*skip*/
  x4 = _br_load(in1+0);
  x5 = _br_load(in1+8);
  x6 = _br_load(in1+16);
  x7 = _br_load(in1+24);
  /*skip*/
  /*skip*/
  x8 = x1;
  x9 = x2;
  x10 = x3;
  x11 = x0;
  x12 = x11*x7;
  x13 = _br_mulhuu(x11, x7);
  x14 = x11*x6;
  x15 = _br_mulhuu(x11, x6);
  x16 = x11*x5;
  x17 = _br_mulhuu(x11, x5);
  x18 = x11*x4;
  x19 = _br_mulhuu(x11, x4);
  x20 = x19+x16;
  x21 = (br_word_t)(x20<x19);
  x22 = x21+x17;
  x23 = (br_word_t)(x22<x17);
  x24 = x22+x14;
  x25 = (br_word_t)(x24<x14);
  x26 = x23+x25;
  x27 = x26+x15;
  x28 = (br_word_t)(x27<x15);
  x29 = x27+x12;
  x30 = (br_word_t)(x29<x12);
  x31 = x28+x30;
  x32 = x31+x13;
  x33 = x18*0x2387f9007f17daa9;
  x34 = x33*0x8fb501e34aa387f9;
  x35 = _br_mulhuu(x33, (br_word_t)0x8fb501e34aa387f9);
  x36 = x33*0xaa6fecb86184dc21;
  x37 = _br_mulhuu(x33, (br_word_t)0xaa6fecb86184dc21);
  x38 = x33*0xee5b88d120b5b59e ;
  x39 = _br_mulhuu(x33, (br_word_t)0xee5b88d120b5b59e );
  x40 = x33*0x185cac6c5e089667;
  x41 = _br_mulhuu(x33, (br_word_t)0x185cac6c5e089667);
  x42 = x41+x38;
  x43 = (br_word_t)(x42<x41);
  x44 = x43+x39;
  x45 = (br_word_t)(x44<x39);
  x46 = x44+x36;
  x47 = (br_word_t)(x46<x36);
  x48 = x45+x47;
  x49 = x48+x37;
  x50 = (br_word_t)(x49<x37);
  x51 = x49+x34;
  x52 = (br_word_t)(x51<x34);
  x53 = x50+x52;
  x54 = x53+x35;
  x55 = x18+x40;
  x56 = (br_word_t)(x55<x18);
  x57 = x56+x20;
  x58 = (br_word_t)(x57<x20);
  x59 = x57+x42;
  x60 = (br_word_t)(x59<x42);
  x61 = x58+x60;
  x62 = x61+x24;
  x63 = (br_word_t)(x62<x24);
  x64 = x62+x46;
  x65 = (br_word_t)(x64<x46);
  x66 = x63+x65;
  x67 = x66+x29;
  x68 = (br_word_t)(x67<x29);
  x69 = x67+x51;
  x70 = (br_word_t)(x69<x51);
  x71 = x68+x70;
  x72 = x71+x32;
  x73 = (br_word_t)(x72<x32);
  x74 = x72+x54;
  x75 = (br_word_t)(x74<x54);
  x76 = x73+x75;
  x77 = x8*x7;
  x78 = _br_mulhuu(x8, x7);
  x79 = x8*x6;
  x80 = _br_mulhuu(x8, x6);
  x81 = x8*x5;
  x82 = _br_mulhuu(x8, x5);
  x83 = x8*x4;
  x84 = _br_mulhuu(x8, x4);
  x85 = x84+x81;
  x86 = (br_word_t)(x85<x84);
  x87 = x86+x82;
  x88 = (br_word_t)(x87<x82);
  x89 = x87+x79;
  x90 = (br_word_t)(x89<x79);
  x91 = x88+x90;
  x92 = x91+x80;
  x93 = (br_word_t)(x92<x80);
  x94 = x92+x77;
  x95 = (br_word_t)(x94<x77);
  x96 = x93+x95;
  x97 = x96+x78;
  x98 = x59+x83;
  x99 = (br_word_t)(x98<x59);
  x100 = x99+x64;
  x101 = (br_word_t)(x100<x64);
  x102 = x100+x85;
  x103 = (br_word_t)(x102<x85);
  x104 = x101+x103;
  x105 = x104+x69;
  x106 = (br_word_t)(x105<x69);
  x107 = x105+x89;
  x108 = (br_word_t)(x107<x89);
  x109 = x106+x108;
  x110 = x109+x74;
  x111 = (br_word_t)(x110<x74);
  x112 = x110+x94;
  x113 = (br_word_t)(x112<x94);
  x114 = x111+x113;
  x115 = x114+x76;
  x116 = (br_word_t)(x115<x76);
  x117 = x115+x97;
  x118 = (br_word_t)(x117<x97);
  x119 = x116+x118;
  x120 = x98*0x2387f9007f17daa9;
  x121 = x120*0x8fb501e34aa387f9;
  x122 = _br_mulhuu(x120, (br_word_t)0x8fb501e34aa387f9);
  x123 = x120*0xaa6fecb86184dc21;
  x124 = _br_mulhuu(x120, (br_word_t)0xaa6fecb86184dc21);
  x125 = x120*0xee5b88d120b5b59e ;
  x126 = _br_mulhuu(x120, (br_word_t)0xee5b88d120b5b59e );
  x127 = x120*0x185cac6c5e089667;
  x128 = _br_mulhuu(x120, (br_word_t)0x185cac6c5e089667);
  x129 = x128+x125;
  x130 = (br_word_t)(x129<x128);
  x131 = x130+x126;
  x132 = (br_word_t)(x131<x126);
  x133 = x131+x123;
  x134 = (br_word_t)(x133<x123);
  x135 = x132+x134;
  x136 = x135+x124;
  x137 = (br_word_t)(x136<x124);
  x138 = x136+x121;
  x139 = (br_word_t)(x138<x121);
  x140 = x137+x139;
  x141 = x140+x122;
  x142 = x98+x127;
  x143 = (br_word_t)(x142<x98);
  x144 = x143+x102;
  x145 = (br_word_t)(x144<x102);
  x146 = x144+x129;
  x147 = (br_word_t)(x146<x129);
  x148 = x145+x147;
  x149 = x148+x107;
  x150 = (br_word_t)(x149<x107);
  x151 = x149+x133;
  x152 = (br_word_t)(x151<x133);
  x153 = x150+x152;
  x154 = x153+x112;
  x155 = (br_word_t)(x154<x112);
  x156 = x154+x138;
  x157 = (br_word_t)(x156<x138);
  x158 = x155+x157;
  x159 = x158+x117;
  x160 = (br_word_t)(x159<x117);
  x161 = x159+x141;
  x162 = (br_word_t)(x161<x141);
  x163 = x160+x162;
  x164 = x163+x119;
  x165 = x9*x7;
  x166 = _br_mulhuu(x9, x7);
  x167 = x9*x6;
  x168 = _br_mulhuu(x9, x6);
  x169 = x9*x5;
  x170 = _br_mulhuu(x9, x5);
  x171 = x9*x4;
  x172 = _br_mulhuu(x9, x4);
  x173 = x172+x169;
  x174 = (br_word_t)(x173<x172);
  x175 = x174+x170;
  x176 = (br_word_t)(x175<x170);
  x177 = x175+x167;
  x178 = (br_word_t)(x177<x167);
  x179 = x176+x178;
  x180 = x179+x168;
  x181 = (br_word_t)(x180<x168);
  x182 = x180+x165;
  x183 = (br_word_t)(x182<x165);
  x184 = x181+x183;
  x185 = x184+x166;
  x186 = x146+x171;
  x187 = (br_word_t)(x186<x146);
  x188 = x187+x151;
  x189 = (br_word_t)(x188<x151);
  x190 = x188+x173;
  x191 = (br_word_t)(x190<x173);
  x192 = x189+x191;
  x193 = x192+x156;
  x194 = (br_word_t)(x193<x156);
  x195 = x193+x177;
  x196 = (br_word_t)(x195<x177);
  x197 = x194+x196;
  x198 = x197+x161;
  x199 = (br_word_t)(x198<x161);
  x200 = x198+x182;
  x201 = (br_word_t)(x200<x182);
  x202 = x199+x201;
  x203 = x202+x164;
  x204 = (br_word_t)(x203<x164);
  x205 = x203+x185;
  x206 = (br_word_t)(x205<x185);
  x207 = x204+x206;
  x208 = x186*0x2387f9007f17daa9;
  x209 = x208*0x8fb501e34aa387f9;
  x210 = _br_mulhuu(x208, (br_word_t)0x8fb501e34aa387f9);
  x211 = x208*0xaa6fecb86184dc21;
  x212 = _br_mulhuu(x208, (br_word_t)0xaa6fecb86184dc21);
  x213 = x208*0xee5b88d120b5b59e ;
  x214 = _br_mulhuu(x208, (br_word_t)0xee5b88d120b5b59e );
  x215 = x208*0x185cac6c5e089667;
  x216 = _br_mulhuu(x208, (br_word_t)0x185cac6c5e089667);
  x217 = x216+x213;
  x218 = (br_word_t)(x217<x216);
  x219 = x218+x214;
  x220 = (br_word_t)(x219<x214);
  x221 = x219+x211;
  x222 = (br_word_t)(x221<x211);
  x223 = x220+x222;
  x224 = x223+x212;
  x225 = (br_word_t)(x224<x212);
  x226 = x224+x209;
  x227 = (br_word_t)(x226<x209);
  x228 = x225+x227;
  x229 = x228+x210;
  x230 = x186+x215;
  x231 = (br_word_t)(x230<x186);
  x232 = x231+x190;
  x233 = (br_word_t)(x232<x190);
  x234 = x232+x217;
  x235 = (br_word_t)(x234<x217);
  x236 = x233+x235;
  x237 = x236+x195;
  x238 = (br_word_t)(x237<x195);
  x239 = x237+x221;
  x240 = (br_word_t)(x239<x221);
  x241 = x238+x240;
  x242 = x241+x200;
  x243 = (br_word_t)(x242<x200);
  x244 = x242+x226;
  x245 = (br_word_t)(x244<x226);
  x246 = x243+x245;
  x247 = x246+x205;
  x248 = (br_word_t)(x247<x205);
  x249 = x247+x229;
  x250 = (br_word_t)(x249<x229);
  x251 = x248+x250;
  x252 = x251+x207;
  x253 = x10*x7;
  x254 = _br_mulhuu(x10, x7);
  x255 = x10*x6;
  x256 = _br_mulhuu(x10, x6);
  x257 = x10*x5;
  x258 = _br_mulhuu(x10, x5);
  x259 = x10*x4;
  x260 = _br_mulhuu(x10, x4);
  x261 = x260+x257;
  x262 = (br_word_t)(x261<x260);
  x263 = x262+x258;
  x264 = (br_word_t)(x263<x258);
  x265 = x263+x255;
  x266 = (br_word_t)(x265<x255);
  x267 = x264+x266;
  x268 = x267+x256;
  x269 = (br_word_t)(x268<x256);
  x270 = x268+x253;
  x271 = (br_word_t)(x270<x253);
  x272 = x269+x271;
  x273 = x272+x254;
  x274 = x234+x259;
  x275 = (br_word_t)(x274<x234);
  x276 = x275+x239;
  x277 = (br_word_t)(x276<x239);
  x278 = x276+x261;
  x279 = (br_word_t)(x278<x261);
  x280 = x277+x279;
  x281 = x280+x244;
  x282 = (br_word_t)(x281<x244);
  x283 = x281+x265;
  x284 = (br_word_t)(x283<x265);
  x285 = x282+x284;
  x286 = x285+x249;
  x287 = (br_word_t)(x286<x249);
  x288 = x286+x270;
  x289 = (br_word_t)(x288<x270);
  x290 = x287+x289;
  x291 = x290+x252;
  x292 = (br_word_t)(x291<x252);
  x293 = x291+x273;
  x294 = (br_word_t)(x293<x273);
  x295 = x292+x294;
  x296 = x274*0x2387f9007f17daa9;
  x297 = x296*0x8fb501e34aa387f9;
  x298 = _br_mulhuu(x296, (br_word_t)0x8fb501e34aa387f9);
  x299 = x296*0xaa6fecb86184dc21;
  x300 = _br_mulhuu(x296, (br_word_t)0xaa6fecb86184dc21);
  x301 = x296*0xee5b88d120b5b59e ;
  x302 = _br_mulhuu(x296, (br_word_t)0xee5b88d120b5b59e );
  x303 = x296*0x185cac6c5e089667;
  x304 = _br_mulhuu(x296, (br_word_t)0x185cac6c5e089667);
  x305 = x304+x301;
  x306 = (br_word_t)(x305<x304);
  x307 = x306+x302;
  x308 = (br_word_t)(x307<x302);
  x309 = x307+x299;
  x310 = (br_word_t)(x309<x299);
  x311 = x308+x310;
  x312 = x311+x300;
  x313 = (br_word_t)(x312<x300);
  x314 = x312+x297;
  x315 = (br_word_t)(x314<x297);
  x316 = x313+x315;
  x317 = x316+x298;
  x318 = x274+x303;
  x319 = (br_word_t)(x318<x274);
  x320 = x319+x278;
  x321 = (br_word_t)(x320<x278);
  x322 = x320+x305;
  x323 = (br_word_t)(x322<x305);
  x324 = x321+x323;
  x325 = x324+x283;
  x326 = (br_word_t)(x325<x283);
  x327 = x325+x309;
  x328 = (br_word_t)(x327<x309);
  x329 = x326+x328;
  x330 = x329+x288;
  x331 = (br_word_t)(x330<x288);
  x332 = x330+x314;
  x333 = (br_word_t)(x332<x314);
  x334 = x331+x333;
  x335 = x334+x293;
  x336 = (br_word_t)(x335<x293);
  x337 = x335+x317;
  x338 = (br_word_t)(x337<x317);
  x339 = x336+x338;
  x340 = x339+x295;
  x341 = x322-0x185cac6c5e089667;
  x342 = (br_word_t)(x322<x341);
  x343 = x327-0xee5b88d120b5b59e ;
  x344 = (br_word_t)(x327<x343);
  x345 = x343-x342;
  x346 = (br_word_t)(x343<x345);
  x347 = x344+x346;
  x348 = x332-0xaa6fecb86184dc21;
  x349 = (br_word_t)(x332<x348);
  x350 = x348-x347;
  x351 = (br_word_t)(x348<x350);
  x352 = x349+x351;
  x353 = x337-0x8fb501e34aa387f9;
  x354 = (br_word_t)(x337<x353);
  x355 = x353-x352;
  x356 = (br_word_t)(x353<x355);
  x357 = x354+x356;
  x358 = x340-x357;
  x359 = (br_word_t)(x340<x358);
  x360 = (0u-(br_word_t)1)+((br_word_t)(x359==(br_word_t)0));
  x361 = x360^0xffffffffffffffff;
  x362 = (x322&x360)|(x341&x361);
  x363 = (0u-(br_word_t)1)+((br_word_t)(x359==(br_word_t)0));
  x364 = x363^0xffffffffffffffff;
  x365 = (x327&x363)|(x345&x364);
  x366 = (0u-(br_word_t)1)+((br_word_t)(x359==(br_word_t)0));
  x367 = x366^0xffffffffffffffff;
  x368 = (x332&x366)|(x350&x367);
  x369 = (0u-(br_word_t)1)+((br_word_t)(x359==(br_word_t)0));
  x370 = x369^0xffffffffffffffff;
  x371 = (x337&x369)|(x355&x370);
  x372 = x362;
  x373 = x365;
  x374 = x368;
  x375 = x371;
  /*skip*/
  _br_store(out0+0, x372);
  _br_store(out0+8, x373);
  _br_store(out0+16, x374);
  _br_store(out0+24, x375);
  /*skip*/
}

static void bn256_square(br_word_t out0, br_word_t in0) {
  br_word_t x7, x12, x15, x17, x13, x18, x10, x19, x21, x22, x11, x23, x8, x24, x26, x27, x9, x29, x34, x37, x39, x35, x40, x32, x41, x43, x44, x33, x45, x30, x46, x48, x49, x31, x36, x51, x14, x52, x16, x53, x38, x54, x56, x57, x20, x58, x42, x59, x61, x62, x25, x63, x47, x64, x66, x67, x28, x68, x50, x69, x71, x4, x77, x80, x82, x78, x83, x75, x84, x86, x87, x76, x88, x73, x89, x91, x92, x74, x79, x55, x95, x60, x96, x81, x97, x99, x100, x65, x101, x85, x102, x104, x105, x70, x106, x90, x107, x109, x110, x72, x111, x93, x112, x114, x116, x121, x124, x126, x122, x127, x119, x128, x130, x131, x120, x132, x117, x133, x135, x136, x118, x123, x138, x94, x139, x98, x140, x125, x141, x143, x144, x103, x145, x129, x146, x148, x149, x108, x150, x134, x151, x153, x154, x113, x155, x137, x156, x158, x159, x115, x5, x165, x168, x170, x166, x171, x163, x172, x174, x175, x164, x176, x161, x177, x179, x180, x162, x167, x142, x183, x147, x184, x169, x185, x187, x188, x152, x189, x173, x190, x192, x193, x157, x194, x178, x195, x197, x198, x160, x199, x181, x200, x202, x204, x209, x212, x214, x210, x215, x207, x216, x218, x219, x208, x220, x205, x221, x223, x224, x206, x211, x226, x182, x227, x186, x228, x213, x229, x231, x232, x191, x233, x217, x234, x236, x237, x196, x238, x222, x239, x241, x242, x201, x243, x225, x244, x246, x247, x203, x3, x2, x1, x6, x0, x253, x256, x258, x254, x259, x251, x260, x262, x263, x252, x264, x249, x265, x267, x268, x250, x255, x230, x271, x235, x272, x257, x273, x275, x276, x240, x277, x261, x278, x280, x281, x245, x282, x266, x283, x285, x286, x248, x287, x269, x288, x290, x292, x297, x300, x302, x298, x303, x295, x304, x306, x307, x296, x308, x293, x309, x311, x312, x294, x299, x314, x270, x315, x274, x316, x301, x317, x319, x320, x279, x321, x305, x322, x324, x325, x284, x326, x310, x327, x329, x330, x289, x331, x313, x332, x334, x335, x291, x338, x339, x340, x342, x343, x344, x345, x347, x348, x349, x350, x352, x353, x336, x354, x318, x356, x337, x357, x323, x359, x341, x360, x328, x362, x346, x363, x355, x333, x365, x351, x366, x358, x361, x364, x367, x368, x369, x370, x371;
  x0 = _br_load(in0+0);
  x1 = _br_load(in0+8);
  x2 = _br_load(in0+16);
  x3 = _br_load(in0+24);
  /*skip*/
  /*skip*/
  x4 = x1;
  x5 = x2;
  x6 = x3;
  x7 = x0;
  x8 = x7*x3;
  x9 = _br_mulhuu(x7, x3);
  x10 = x7*x2;
  x11 = _br_mulhuu(x7, x2);
  x12 = x7*x1;
  x13 = _br_mulhuu(x7, x1);
  x14 = x7*x0;
  x15 = _br_mulhuu(x7, x0);
  x16 = x15+x12;
  x17 = (br_word_t)(x16<x15);
  x18 = x17+x13;
  x19 = (br_word_t)(x18<x13);
  x20 = x18+x10;
  x21 = (br_word_t)(x20<x10);
  x22 = x19+x21;
  x23 = x22+x11;
  x24 = (br_word_t)(x23<x11);
  x25 = x23+x8;
  x26 = (br_word_t)(x25<x8);
  x27 = x24+x26;
  x28 = x27+x9;
  x29 = x14*0x2387f9007f17daa9;
  x30 = x29*0x8fb501e34aa387f9;
  x31 = _br_mulhuu(x29, (br_word_t)0x8fb501e34aa387f9);
  x32 = x29*0xaa6fecb86184dc21;
  x33 = _br_mulhuu(x29, (br_word_t)0xaa6fecb86184dc21);
  x34 = x29*0xee5b88d120b5b59e ;
  x35 = _br_mulhuu(x29, (br_word_t)0xee5b88d120b5b59e );
  x36 = x29*0x185cac6c5e089667;
  x37 = _br_mulhuu(x29, (br_word_t)0x185cac6c5e089667);
  x38 = x37+x34;
  x39 = (br_word_t)(x38<x37);
  x40 = x39+x35;
  x41 = (br_word_t)(x40<x35);
  x42 = x40+x32;
  x43 = (br_word_t)(x42<x32);
  x44 = x41+x43;
  x45 = x44+x33;
  x46 = (br_word_t)(x45<x33);
  x47 = x45+x30;
  x48 = (br_word_t)(x47<x30);
  x49 = x46+x48;
  x50 = x49+x31;
  x51 = x14+x36;
  x52 = (br_word_t)(x51<x14);
  x53 = x52+x16;
  x54 = (br_word_t)(x53<x16);
  x55 = x53+x38;
  x56 = (br_word_t)(x55<x38);
  x57 = x54+x56;
  x58 = x57+x20;
  x59 = (br_word_t)(x58<x20);
  x60 = x58+x42;
  x61 = (br_word_t)(x60<x42);
  x62 = x59+x61;
  x63 = x62+x25;
  x64 = (br_word_t)(x63<x25);
  x65 = x63+x47;
  x66 = (br_word_t)(x65<x47);
  x67 = x64+x66;
  x68 = x67+x28;
  x69 = (br_word_t)(x68<x28);
  x70 = x68+x50;
  x71 = (br_word_t)(x70<x50);
  x72 = x69+x71;
  x73 = x4*x3;
  x74 = _br_mulhuu(x4, x3);
  x75 = x4*x2;
  x76 = _br_mulhuu(x4, x2);
  x77 = x4*x1;
  x78 = _br_mulhuu(x4, x1);
  x79 = x4*x0;
  x80 = _br_mulhuu(x4, x0);
  x81 = x80+x77;
  x82 = (br_word_t)(x81<x80);
  x83 = x82+x78;
  x84 = (br_word_t)(x83<x78);
  x85 = x83+x75;
  x86 = (br_word_t)(x85<x75);
  x87 = x84+x86;
  x88 = x87+x76;
  x89 = (br_word_t)(x88<x76);
  x90 = x88+x73;
  x91 = (br_word_t)(x90<x73);
  x92 = x89+x91;
  x93 = x92+x74;
  x94 = x55+x79;
  x95 = (br_word_t)(x94<x55);
  x96 = x95+x60;
  x97 = (br_word_t)(x96<x60);
  x98 = x96+x81;
  x99 = (br_word_t)(x98<x81);
  x100 = x97+x99;
  x101 = x100+x65;
  x102 = (br_word_t)(x101<x65);
  x103 = x101+x85;
  x104 = (br_word_t)(x103<x85);
  x105 = x102+x104;
  x106 = x105+x70;
  x107 = (br_word_t)(x106<x70);
  x108 = x106+x90;
  x109 = (br_word_t)(x108<x90);
  x110 = x107+x109;
  x111 = x110+x72;
  x112 = (br_word_t)(x111<x72);
  x113 = x111+x93;
  x114 = (br_word_t)(x113<x93);
  x115 = x112+x114;
  x116 = x94*0x2387f9007f17daa9;
  x117 = x116*0x8fb501e34aa387f9;
  x118 = _br_mulhuu(x116, (br_word_t)0x8fb501e34aa387f9);
  x119 = x116*0xaa6fecb86184dc21;
  x120 = _br_mulhuu(x116, (br_word_t)0xaa6fecb86184dc21);
  x121 = x116*0xee5b88d120b5b59e ;
  x122 = _br_mulhuu(x116, (br_word_t)0xee5b88d120b5b59e );
  x123 = x116*0x185cac6c5e089667;
  x124 = _br_mulhuu(x116, (br_word_t)0x185cac6c5e089667);
  x125 = x124+x121;
  x126 = (br_word_t)(x125<x124);
  x127 = x126+x122;
  x128 = (br_word_t)(x127<x122);
  x129 = x127+x119;
  x130 = (br_word_t)(x129<x119);
  x131 = x128+x130;
  x132 = x131+x120;
  x133 = (br_word_t)(x132<x120);
  x134 = x132+x117;
  x135 = (br_word_t)(x134<x117);
  x136 = x133+x135;
  x137 = x136+x118;
  x138 = x94+x123;
  x139 = (br_word_t)(x138<x94);
  x140 = x139+x98;
  x141 = (br_word_t)(x140<x98);
  x142 = x140+x125;
  x143 = (br_word_t)(x142<x125);
  x144 = x141+x143;
  x145 = x144+x103;
  x146 = (br_word_t)(x145<x103);
  x147 = x145+x129;
  x148 = (br_word_t)(x147<x129);
  x149 = x146+x148;
  x150 = x149+x108;
  x151 = (br_word_t)(x150<x108);
  x152 = x150+x134;
  x153 = (br_word_t)(x152<x134);
  x154 = x151+x153;
  x155 = x154+x113;
  x156 = (br_word_t)(x155<x113);
  x157 = x155+x137;
  x158 = (br_word_t)(x157<x137);
  x159 = x156+x158;
  x160 = x159+x115;
  x161 = x5*x3;
  x162 = _br_mulhuu(x5, x3);
  x163 = x5*x2;
  x164 = _br_mulhuu(x5, x2);
  x165 = x5*x1;
  x166 = _br_mulhuu(x5, x1);
  x167 = x5*x0;
  x168 = _br_mulhuu(x5, x0);
  x169 = x168+x165;
  x170 = (br_word_t)(x169<x168);
  x171 = x170+x166;
  x172 = (br_word_t)(x171<x166);
  x173 = x171+x163;
  x174 = (br_word_t)(x173<x163);
  x175 = x172+x174;
  x176 = x175+x164;
  x177 = (br_word_t)(x176<x164);
  x178 = x176+x161;
  x179 = (br_word_t)(x178<x161);
  x180 = x177+x179;
  x181 = x180+x162;
  x182 = x142+x167;
  x183 = (br_word_t)(x182<x142);
  x184 = x183+x147;
  x185 = (br_word_t)(x184<x147);
  x186 = x184+x169;
  x187 = (br_word_t)(x186<x169);
  x188 = x185+x187;
  x189 = x188+x152;
  x190 = (br_word_t)(x189<x152);
  x191 = x189+x173;
  x192 = (br_word_t)(x191<x173);
  x193 = x190+x192;
  x194 = x193+x157;
  x195 = (br_word_t)(x194<x157);
  x196 = x194+x178;
  x197 = (br_word_t)(x196<x178);
  x198 = x195+x197;
  x199 = x198+x160;
  x200 = (br_word_t)(x199<x160);
  x201 = x199+x181;
  x202 = (br_word_t)(x201<x181);
  x203 = x200+x202;
  x204 = x182*0x2387f9007f17daa9;
  x205 = x204*0x8fb501e34aa387f9;
  x206 = _br_mulhuu(x204, (br_word_t)0x8fb501e34aa387f9);
  x207 = x204*0xaa6fecb86184dc21;
  x208 = _br_mulhuu(x204, (br_word_t)0xaa6fecb86184dc21);
  x209 = x204*0xee5b88d120b5b59e ;
  x210 = _br_mulhuu(x204, (br_word_t)0xee5b88d120b5b59e );
  x211 = x204*0x185cac6c5e089667;
  x212 = _br_mulhuu(x204, (br_word_t)0x185cac6c5e089667);
  x213 = x212+x209;
  x214 = (br_word_t)(x213<x212);
  x215 = x214+x210;
  x216 = (br_word_t)(x215<x210);
  x217 = x215+x207;
  x218 = (br_word_t)(x217<x207);
  x219 = x216+x218;
  x220 = x219+x208;
  x221 = (br_word_t)(x220<x208);
  x222 = x220+x205;
  x223 = (br_word_t)(x222<x205);
  x224 = x221+x223;
  x225 = x224+x206;
  x226 = x182+x211;
  x227 = (br_word_t)(x226<x182);
  x228 = x227+x186;
  x229 = (br_word_t)(x228<x186);
  x230 = x228+x213;
  x231 = (br_word_t)(x230<x213);
  x232 = x229+x231;
  x233 = x232+x191;
  x234 = (br_word_t)(x233<x191);
  x235 = x233+x217;
  x236 = (br_word_t)(x235<x217);
  x237 = x234+x236;
  x238 = x237+x196;
  x239 = (br_word_t)(x238<x196);
  x240 = x238+x222;
  x241 = (br_word_t)(x240<x222);
  x242 = x239+x241;
  x243 = x242+x201;
  x244 = (br_word_t)(x243<x201);
  x245 = x243+x225;
  x246 = (br_word_t)(x245<x225);
  x247 = x244+x246;
  x248 = x247+x203;
  x249 = x6*x3;
  x250 = _br_mulhuu(x6, x3);
  x251 = x6*x2;
  x252 = _br_mulhuu(x6, x2);
  x253 = x6*x1;
  x254 = _br_mulhuu(x6, x1);
  x255 = x6*x0;
  x256 = _br_mulhuu(x6, x0);
  x257 = x256+x253;
  x258 = (br_word_t)(x257<x256);
  x259 = x258+x254;
  x260 = (br_word_t)(x259<x254);
  x261 = x259+x251;
  x262 = (br_word_t)(x261<x251);
  x263 = x260+x262;
  x264 = x263+x252;
  x265 = (br_word_t)(x264<x252);
  x266 = x264+x249;
  x267 = (br_word_t)(x266<x249);
  x268 = x265+x267;
  x269 = x268+x250;
  x270 = x230+x255;
  x271 = (br_word_t)(x270<x230);
  x272 = x271+x235;
  x273 = (br_word_t)(x272<x235);
  x274 = x272+x257;
  x275 = (br_word_t)(x274<x257);
  x276 = x273+x275;
  x277 = x276+x240;
  x278 = (br_word_t)(x277<x240);
  x279 = x277+x261;
  x280 = (br_word_t)(x279<x261);
  x281 = x278+x280;
  x282 = x281+x245;
  x283 = (br_word_t)(x282<x245);
  x284 = x282+x266;
  x285 = (br_word_t)(x284<x266);
  x286 = x283+x285;
  x287 = x286+x248;
  x288 = (br_word_t)(x287<x248);
  x289 = x287+x269;
  x290 = (br_word_t)(x289<x269);
  x291 = x288+x290;
  x292 = x270*0x2387f9007f17daa9;
  x293 = x292*0x8fb501e34aa387f9;
  x294 = _br_mulhuu(x292, (br_word_t)0x8fb501e34aa387f9);
  x295 = x292*0xaa6fecb86184dc21;
  x296 = _br_mulhuu(x292, (br_word_t)0xaa6fecb86184dc21);
  x297 = x292*0xee5b88d120b5b59e ;
  x298 = _br_mulhuu(x292, (br_word_t)0xee5b88d120b5b59e );
  x299 = x292*0x185cac6c5e089667;
  x300 = _br_mulhuu(x292, (br_word_t)0x185cac6c5e089667);
  x301 = x300+x297;
  x302 = (br_word_t)(x301<x300);
  x303 = x302+x298;
  x304 = (br_word_t)(x303<x298);
  x305 = x303+x295;
  x306 = (br_word_t)(x305<x295);
  x307 = x304+x306;
  x308 = x307+x296;
  x309 = (br_word_t)(x308<x296);
  x310 = x308+x293;
  x311 = (br_word_t)(x310<x293);
  x312 = x309+x311;
  x313 = x312+x294;
  x314 = x270+x299;
  x315 = (br_word_t)(x314<x270);
  x316 = x315+x274;
  x317 = (br_word_t)(x316<x274);
  x318 = x316+x301;
  x319 = (br_word_t)(x318<x301);
  x320 = x317+x319;
  x321 = x320+x279;
  x322 = (br_word_t)(x321<x279);
  x323 = x321+x305;
  x324 = (br_word_t)(x323<x305);
  x325 = x322+x324;
  x326 = x325+x284;
  x327 = (br_word_t)(x326<x284);
  x328 = x326+x310;
  x329 = (br_word_t)(x328<x310);
  x330 = x327+x329;
  x331 = x330+x289;
  x332 = (br_word_t)(x331<x289);
  x333 = x331+x313;
  x334 = (br_word_t)(x333<x313);
  x335 = x332+x334;
  x336 = x335+x291;
  x337 = x318-0x185cac6c5e089667;
  x338 = (br_word_t)(x318<x337);
  x339 = x323-0xee5b88d120b5b59e ;
  x340 = (br_word_t)(x323<x339);
  x341 = x339-x338;
  x342 = (br_word_t)(x339<x341);
  x343 = x340+x342;
  x344 = x328-0xaa6fecb86184dc21;
  x345 = (br_word_t)(x328<x344);
  x346 = x344-x343;
  x347 = (br_word_t)(x344<x346);
  x348 = x345+x347;
  x349 = x333-0x8fb501e34aa387f9;
  x350 = (br_word_t)(x333<x349);
  x351 = x349-x348;
  x352 = (br_word_t)(x349<x351);
  x353 = x350+x352;
  x354 = x336-x353;
  x355 = (br_word_t)(x336<x354);
  x356 = (0u-(br_word_t)1)+((br_word_t)(x355==(br_word_t)0));
  x357 = x356^0xffffffffffffffff;
  x358 = (x318&x356)|(x337&x357);
  x359 = (0u-(br_word_t)1)+((br_word_t)(x355==(br_word_t)0));
  x360 = x359^0xffffffffffffffff;
  x361 = (x323&x359)|(x341&x360);
  x362 = (0u-(br_word_t)1)+((br_word_t)(x355==(br_word_t)0));
  x363 = x362^0xffffffffffffffff;
  x364 = (x328&x362)|(x346&x363);
  x365 = (0u-(br_word_t)1)+((br_word_t)(x355==(br_word_t)0));
  x366 = x365^0xffffffffffffffff;
  x367 = (x333&x365)|(x351&x366);
  x368 = x358;
  x369 = x361;
  x370 = x364;
  x371 = x367;
  /*skip*/
  _br_store(out0+0, x368);
  _br_store(out0+8, x369);
  _br_store(out0+16, x370);
  _br_store(out0+24, x371);
  /*skip*/
}

static void bn256_select_znz(br_word_t out0, br_word_t in0, br_word_t in1, br_word_t in2) {
  br_word_t x4, x8, x0, x9, x5, x11, x1, x12, x6, x14, x2, x15, x7, x17, x3, x18, x10, x13, x16, x19, x20, x21, x22, x23;
  /*skip*/
  x0 = _br_load(in1+0);
  x1 = _br_load(in1+8);
  x2 = _br_load(in1+16);
  x3 = _br_load(in1+24);
  /*skip*/
  x4 = _br_load(in2+0);
  x5 = _br_load(in2+8);
  x6 = _br_load(in2+16);
  x7 = _br_load(in2+24);
  /*skip*/
  /*skip*/
  x8 = (0u-(br_word_t)1)+((br_word_t)(in0==(br_word_t)0));
  x9 = x8^0xffffffffffffffff;
  x10 = (x4&x8)|(x0&x9);
  x11 = (0u-(br_word_t)1)+((br_word_t)(in0==(br_word_t)0));
  x12 = x11^0xffffffffffffffff;
  x13 = (x5&x11)|(x1&x12);
  x14 = (0u-(br_word_t)1)+((br_word_t)(in0==(br_word_t)0));
  x15 = x14^0xffffffffffffffff;
  x16 = (x6&x14)|(x2&x15);
  x17 = (0u-(br_word_t)1)+((br_word_t)(in0==(br_word_t)0));
  x18 = x17^0xffffffffffffffff;
  x19 = (x7&x17)|(x3&x18);
  x20 = x10;
  x21 = x13;
  x22 = x16;
  x23 = x19;
  /*skip*/
  _br_store(out0+0, x20);
  _br_store(out0+8, x21);
  _br_store(out0+16, x22);
  _br_store(out0+24, x23);
  /*skip*/
}

static void bn256_felem_copy(br_word_t out, br_word_t in) {
  _br_store(out, _br_load(in));
  _br_store(out+8, _br_load(in+8));
  _br_store(out+16, _br_load(in+16));
  _br_store(out+24, _br_load(in+24));
}

static void bn256_Fp2_mul_xi(br_word_t out, br_word_t x) {
  br_word_t tmp_a3, tmp_b3;
  uint8_t _br_stackalloc_tmp_a3[32] = {0}; tmp_a3 = (br_word_t)&_br_stackalloc_tmp_a3;
  uint8_t _br_stackalloc_tmp_b3[32] = {0}; tmp_b3 = (br_word_t)&_br_stackalloc_tmp_b3;
  bn256_add(tmp_a3, x, x);
  bn256_add(tmp_a3, tmp_a3, x);
  bn256_add(tmp_b3, x+32, x+32);
  bn256_add(tmp_b3, tmp_b3, x+32);
  bn256_sub(out, tmp_a3, x+32);
  bn256_add(out+32, x, tmp_b3);
}

static void bn256_Fp6_felem_copy(br_word_t out, br_word_t x) {
  bn256_Fp2_felem_copy(out, x);
  bn256_Fp2_felem_copy(out+64, x+64);
  bn256_Fp2_felem_copy(out+128, x+128);
}

static void bn256_Fp6_add(br_word_t out, br_word_t inx, br_word_t iny) {
  br_word_t allocx, allocy;
  uint8_t _br_stackalloc_allocx[192] = {0}; allocx = (br_word_t)&_br_stackalloc_allocx;
  uint8_t _br_stackalloc_allocy[192] = {0}; allocy = (br_word_t)&_br_stackalloc_allocy;
  bn256_Fp6_felem_copy(allocx, inx);
  bn256_Fp6_felem_copy(allocy, iny);
  bn256_Fp2_add(out, allocx, allocy);
  bn256_Fp2_add(out+64, allocx+64, allocy+64);
  bn256_Fp2_add(out+128, allocx+128, allocy+128);
}

static void bn256_Fp6_sub(br_word_t out, br_word_t inx, br_word_t iny) {
  br_word_t allocx, allocy;
  uint8_t _br_stackalloc_allocx[192] = {0}; allocx = (br_word_t)&_br_stackalloc_allocx;
  uint8_t _br_stackalloc_allocy[192] = {0}; allocy = (br_word_t)&_br_stackalloc_allocy;
  bn256_Fp6_felem_copy(allocx, inx);
  bn256_Fp6_felem_copy(allocy, iny);
  bn256_Fp2_sub(out, allocx, allocy);
  bn256_Fp2_sub(out+64, allocx+64, allocy+64);
  bn256_Fp2_sub(out+128, allocx+128, allocy+128);
}

static void bn256_Fp6_opp(br_word_t out, br_word_t x) {
  br_word_t allocx;
  uint8_t _br_stackalloc_allocx[192] = {0}; allocx = (br_word_t)&_br_stackalloc_allocx;
  bn256_Fp6_felem_copy(allocx, x);
  bn256_Fp2_opp(out, allocx);
  bn256_Fp2_opp(out+64, allocx+64);
  bn256_Fp2_opp(out+128, allocx+128);
}

static void bn256_Fp6_mul(br_word_t out, br_word_t inx, br_word_t iny) {
  br_word_t allocx, allocy, u, a0b0, a2b2, t, a1b1;
  uint8_t _br_stackalloc_allocx[192] = {0}; allocx = (br_word_t)&_br_stackalloc_allocx;
  uint8_t _br_stackalloc_allocy[192] = {0}; allocy = (br_word_t)&_br_stackalloc_allocy;
  uint8_t _br_stackalloc_a0b0[64] = {0}; a0b0 = (br_word_t)&_br_stackalloc_a0b0;
  uint8_t _br_stackalloc_a1b1[64] = {0}; a1b1 = (br_word_t)&_br_stackalloc_a1b1;
  uint8_t _br_stackalloc_a2b2[64] = {0}; a2b2 = (br_word_t)&_br_stackalloc_a2b2;
  uint8_t _br_stackalloc_t[64] = {0}; t = (br_word_t)&_br_stackalloc_t;
  uint8_t _br_stackalloc_u[64] = {0}; u = (br_word_t)&_br_stackalloc_u;
  bn256_Fp6_felem_copy(allocx, inx);
  bn256_Fp6_felem_copy(allocy, iny);
  bn256_Fp2_mul(a0b0, allocx, allocy);
  bn256_Fp2_mul(a1b1, allocx+64, allocy+64);
  bn256_Fp2_mul(a2b2, allocx+128, allocy+128);
  bn256_Fp2_add(t, allocx+64, allocx+128);
  bn256_Fp2_add(u, allocy+64, allocy+128);
  bn256_Fp2_mul(t, t, u);
  bn256_Fp2_sub(t, t, a1b1);
  bn256_Fp2_sub(t, t, a2b2);
  bn256_Fp2_mul_xi(t, t);
  bn256_Fp2_add(out, a0b0, t);
  bn256_Fp2_add(t, allocx, allocx+64);
  bn256_Fp2_add(u, allocy, allocy+64);
  bn256_Fp2_mul(t, t, u);
  bn256_Fp2_sub(t, t, a0b0);
  bn256_Fp2_sub(t, t, a1b1);
  bn256_Fp2_mul_xi(u, a2b2);
  bn256_Fp2_add(out+64, t, u);
  bn256_Fp2_add(t, allocx, allocx+128);
  bn256_Fp2_add(u, allocy, allocy+128);
  bn256_Fp2_mul(t, t, u);
  bn256_Fp2_sub(t, t, a0b0);
  bn256_Fp2_sub(t, t, a2b2);
  bn256_Fp2_add(out+128, t, a1b1);
}

static void bn256_Fp6_square(br_word_t out, br_word_t x) {
  br_word_t allocx, s1, s2, s3, s0, t, s4;
  uint8_t _br_stackalloc_allocx[192] = {0}; allocx = (br_word_t)&_br_stackalloc_allocx;
  uint8_t _br_stackalloc_s0[64] = {0}; s0 = (br_word_t)&_br_stackalloc_s0;
  uint8_t _br_stackalloc_s1[64] = {0}; s1 = (br_word_t)&_br_stackalloc_s1;
  uint8_t _br_stackalloc_s2[64] = {0}; s2 = (br_word_t)&_br_stackalloc_s2;
  uint8_t _br_stackalloc_s3[64] = {0}; s3 = (br_word_t)&_br_stackalloc_s3;
  uint8_t _br_stackalloc_s4[64] = {0}; s4 = (br_word_t)&_br_stackalloc_s4;
  uint8_t _br_stackalloc_t[64] = {0}; t = (br_word_t)&_br_stackalloc_t;
  bn256_Fp6_felem_copy(allocx, x);
  bn256_Fp2_square(s0, allocx);
  bn256_Fp2_mul(t, allocx, allocx+64);
  bn256_Fp2_add(s1, t, t);
  bn256_Fp2_sub(t, allocx, allocx+64);
  bn256_Fp2_add(t, t, allocx+128);
  bn256_Fp2_square(s2, t);
  bn256_Fp2_mul(t, allocx+64, allocx+128);
  bn256_Fp2_add(s3, t, t);
  bn256_Fp2_square(s4, allocx+128);
  bn256_Fp2_mul_xi(t, s3);
  bn256_Fp2_add(out, s0, t);
  bn256_Fp2_mul_xi(t, s4);
  bn256_Fp2_add(out+64, s1, t);
  bn256_Fp2_add(t, s1, s2);
  bn256_Fp2_add(t, t, s3);
  bn256_Fp2_sub(t, t, s0);
  bn256_Fp2_sub(out+128, t, s4);
}

static void bn256_Fp6_inv(br_word_t out, br_word_t x) {
  br_word_t allocx, t3, t2, vA, vB, vC, t1;
  uint8_t _br_stackalloc_allocx[192] = {0}; allocx = (br_word_t)&_br_stackalloc_allocx;
  uint8_t _br_stackalloc_vA[64] = {0}; vA = (br_word_t)&_br_stackalloc_vA;
  uint8_t _br_stackalloc_vB[64] = {0}; vB = (br_word_t)&_br_stackalloc_vB;
  uint8_t _br_stackalloc_vC[64] = {0}; vC = (br_word_t)&_br_stackalloc_vC;
  uint8_t _br_stackalloc_t1[64] = {0}; t1 = (br_word_t)&_br_stackalloc_t1;
  uint8_t _br_stackalloc_t2[64] = {0}; t2 = (br_word_t)&_br_stackalloc_t2;
  uint8_t _br_stackalloc_t3[64] = {0}; t3 = (br_word_t)&_br_stackalloc_t3;
  bn256_Fp6_felem_copy(allocx, x);
  bn256_Fp2_square(t1, allocx);
  bn256_Fp2_mul(t2, allocx+64, allocx+128);
  bn256_Fp2_mul_xi(t3, t2);
  bn256_Fp2_sub(vA, t1, t3);
  bn256_Fp2_square(t1, allocx+128);
  bn256_Fp2_mul_xi(t3, t1);
  bn256_Fp2_mul(t2, allocx, allocx+64);
  bn256_Fp2_sub(vB, t3, t2);
  bn256_Fp2_square(t1, allocx+64);
  bn256_Fp2_mul(t2, allocx, allocx+128);
  bn256_Fp2_sub(vC, t1, t2);
  bn256_Fp2_mul(t1, allocx, vA);
  bn256_Fp2_mul(t2, allocx+128, vB);
  bn256_Fp2_mul(t3, allocx+64, vC);
  bn256_Fp2_add(t2, t2, t3);
  bn256_Fp2_mul_xi(t2, t2);
  bn256_Fp2_add(t1, t1, t2);
  bn256_Fp2_inv(t1, t1);
  bn256_Fp2_mul(out, vA, t1);
  bn256_Fp2_mul(out+64, vB, t1);
  bn256_Fp2_mul(out+128, vC, t1);
}

static void bn256_Fp6_add_nocopy(br_word_t out, br_word_t inx, br_word_t iny) {
  bn256_Fp2_add(out, inx, iny);
  bn256_Fp2_add(out+64, inx+64, iny+64);
  bn256_Fp2_add(out+128, inx+128, iny+128);
}

static void bn256_Fp6_sub_nocopy(br_word_t out, br_word_t inx, br_word_t iny) {
  bn256_Fp2_sub(out, inx, iny);
  bn256_Fp2_sub(out+64, inx+64, iny+64);
  bn256_Fp2_sub(out+128, inx+128, iny+128);
}

static void bn256_Fp6_mul_by_v(br_word_t out, br_word_t x) {
  br_word_t tmp;
  uint8_t _br_stackalloc_tmp[192] = {0}; tmp = (br_word_t)&_br_stackalloc_tmp;
  bn256_Fp6_felem_copy(tmp, x);
  bn256_Fp2_mul_xi(out, tmp+128);
  bn256_Fp2_felem_copy(out+64, tmp);
  bn256_Fp2_felem_copy(out+128, tmp+64);
}

static void bn256_Fp12_felem_copy(br_word_t out, br_word_t x) {
  bn256_Fp6_felem_copy(out, x);
  bn256_Fp6_felem_copy(out+192, x+192);
}

static void bn256_Fp12_add(br_word_t out, br_word_t inx, br_word_t iny) {
  br_word_t ax, ay;
  uint8_t _br_stackalloc_ax[0x180] = {0}; ax = (br_word_t)&_br_stackalloc_ax;
  uint8_t _br_stackalloc_ay[0x180] = {0}; ay = (br_word_t)&_br_stackalloc_ay;
  bn256_Fp12_felem_copy(ax, inx);
  bn256_Fp12_felem_copy(ay, iny);
  bn256_Fp6_add(out, ax, ay);
  bn256_Fp6_add(out+192, ax+192, ay+192);
}

static void bn256_Fp12_sub(br_word_t out, br_word_t inx, br_word_t iny) {
  br_word_t ax, ay;
  uint8_t _br_stackalloc_ax[0x180] = {0}; ax = (br_word_t)&_br_stackalloc_ax;
  uint8_t _br_stackalloc_ay[0x180] = {0}; ay = (br_word_t)&_br_stackalloc_ay;
  bn256_Fp12_felem_copy(ax, inx);
  bn256_Fp12_felem_copy(ay, iny);
  bn256_Fp6_sub(out, ax, ay);
  bn256_Fp6_sub(out+192, ax+192, ay+192);
}

static void bn256_Fp12_opp(br_word_t out, br_word_t x) {
  br_word_t allocx;
  uint8_t _br_stackalloc_allocx[0x180] = {0}; allocx = (br_word_t)&_br_stackalloc_allocx;
  bn256_Fp12_felem_copy(allocx, x);
  bn256_Fp6_opp(out, allocx);
  bn256_Fp6_opp(out+192, allocx+192);
}

static void bn256_Fp12_conjugate(br_word_t out, br_word_t x) {
  br_word_t allocx;
  uint8_t _br_stackalloc_allocx[0x180] = {0}; allocx = (br_word_t)&_br_stackalloc_allocx;
  bn256_Fp12_felem_copy(allocx, x);
  bn256_Fp6_felem_copy(out, allocx);
  bn256_Fp6_opp(out+192, allocx+192);
}

static void bn256_Fp12_mul(br_word_t out, br_word_t inx, br_word_t iny) {
  br_word_t ax, ay, u, v0, t, v1;
  uint8_t _br_stackalloc_ax[0x180] = {0}; ax = (br_word_t)&_br_stackalloc_ax;
  uint8_t _br_stackalloc_ay[0x180] = {0}; ay = (br_word_t)&_br_stackalloc_ay;
  bn256_Fp12_felem_copy(ax, inx);
  bn256_Fp12_felem_copy(ay, iny);
  uint8_t _br_stackalloc_v0[192] = {0}; v0 = (br_word_t)&_br_stackalloc_v0;
  uint8_t _br_stackalloc_v1[192] = {0}; v1 = (br_word_t)&_br_stackalloc_v1;
  uint8_t _br_stackalloc_t[192] = {0}; t = (br_word_t)&_br_stackalloc_t;
  uint8_t _br_stackalloc_u[192] = {0}; u = (br_word_t)&_br_stackalloc_u;
  bn256_Fp6_mul(v0, ax, ay);
  bn256_Fp6_mul(v1, ax+192, ay+192);
  bn256_Fp6_add(t, ax, ax+192);
  bn256_Fp6_add(u, ay, ay+192);
  bn256_Fp6_mul(t, t, u);
  bn256_Fp6_mul_by_v(u, v1);
  bn256_Fp6_add(out, v0, u);
  bn256_Fp6_sub(t, t, v0);
  bn256_Fp6_sub(out+192, t, v1);
}

static void bn256_Fp12_square(br_word_t out, br_word_t x) {
  br_word_t allocx, t0, t1, t2;
  uint8_t _br_stackalloc_allocx[0x180] = {0}; allocx = (br_word_t)&_br_stackalloc_allocx;
  bn256_Fp12_felem_copy(allocx, x);
  uint8_t _br_stackalloc_t0[192] = {0}; t0 = (br_word_t)&_br_stackalloc_t0;
  uint8_t _br_stackalloc_t1[192] = {0}; t1 = (br_word_t)&_br_stackalloc_t1;
  uint8_t _br_stackalloc_t2[192] = {0}; t2 = (br_word_t)&_br_stackalloc_t2;
  bn256_Fp6_square(t0, allocx);
  bn256_Fp6_square(t1, allocx+192);
  bn256_Fp6_mul(t2, allocx, allocx+192);
  bn256_Fp6_mul_by_v(t1, t1);
  bn256_Fp6_add(out, t0, t1);
  bn256_Fp6_add(out+192, t2, t2);
}

static void bn256_Fp12_inv(br_word_t out, br_word_t x) {
  br_word_t t1, allocx, t0;
  uint8_t _br_stackalloc_allocx[0x180] = {0}; allocx = (br_word_t)&_br_stackalloc_allocx;
  bn256_Fp12_felem_copy(allocx, x);
  uint8_t _br_stackalloc_t0[192] = {0}; t0 = (br_word_t)&_br_stackalloc_t0;
  uint8_t _br_stackalloc_t1[192] = {0}; t1 = (br_word_t)&_br_stackalloc_t1;
  bn256_Fp6_square(t0, allocx);
  bn256_Fp6_square(t1, allocx+192);
  bn256_Fp6_mul_by_v(t1, t1);
  bn256_Fp6_sub(t0, t0, t1);
  bn256_Fp6_inv(t0, t0);
  bn256_Fp6_mul(out, allocx, t0);
  bn256_Fp6_mul(out+192, allocx+192, t0);
  bn256_Fp6_opp(out+192, out+192);
}

static void bn256_Fp12_add_nocopy(br_word_t out, br_word_t inx, br_word_t iny) {
  bn256_Fp6_add(out, inx, iny);
  bn256_Fp6_add(out+192, inx+192, iny+192);
}

static void bn256_Fp12_sub_nocopy(br_word_t out, br_word_t inx, br_word_t iny) {
  bn256_Fp6_sub(out, inx, iny);
  bn256_Fp6_sub(out+192, inx+192, iny+192);
}

static void bn256_Fp12_mul_nocopy(br_word_t out, br_word_t inx, br_word_t iny) {
  br_word_t u, v0, t, v1;
  uint8_t _br_stackalloc_v0[192] = {0}; v0 = (br_word_t)&_br_stackalloc_v0;
  uint8_t _br_stackalloc_v1[192] = {0}; v1 = (br_word_t)&_br_stackalloc_v1;
  uint8_t _br_stackalloc_t[192] = {0}; t = (br_word_t)&_br_stackalloc_t;
  uint8_t _br_stackalloc_u[192] = {0}; u = (br_word_t)&_br_stackalloc_u;
  bn256_Fp6_mul(v0, inx, iny);
  bn256_Fp6_mul(v1, inx+192, iny+192);
  bn256_Fp6_add(t, inx, inx+192);
  bn256_Fp6_add(u, iny, iny+192);
  bn256_Fp6_mul(t, t, u);
  bn256_Fp6_mul_by_v(u, v1);
  bn256_Fp6_add(out, v0, u);
  bn256_Fp6_sub(t, t, v0);
  bn256_Fp6_sub(out+192, t, v1);
}

static void bn256_Fp2_conjugate(br_word_t out, br_word_t x) {
  bn256_felem_copy(out, x);
  bn256_opp(out+32, x+32);
}

static void bn256_Fp6_mul_fp2(br_word_t out, br_word_t x, br_word_t s) {
  br_word_t s_copy;
  uint8_t _br_stackalloc_s_copy[64] = {0}; s_copy = (br_word_t)&_br_stackalloc_s_copy;
  bn256_Fp2_felem_copy(s_copy, s);
  bn256_Fp2_mul(out, x, s_copy);
  bn256_Fp2_mul(out+64, x+64, s_copy);
  bn256_Fp2_mul(out+128, x+128, s_copy);
}

static void bn256_Fp6_frobenius(br_word_t out, br_word_t x, br_word_t gamma1, br_word_t gamma2) {
  br_word_t tmp;
  uint8_t _br_stackalloc_tmp[192] = {0}; tmp = (br_word_t)&_br_stackalloc_tmp;
  bn256_Fp2_conjugate(tmp, x);
  bn256_Fp2_conjugate(tmp+64, x+64);
  bn256_Fp2_conjugate(tmp+128, x+128);
  bn256_Fp2_felem_copy(out, tmp);
  bn256_Fp2_mul(out+64, tmp+64, gamma1);
  bn256_Fp2_mul(out+128, tmp+128, gamma2);
}

static void bn256_Fp6_frobenius_p2(br_word_t out, br_word_t x, br_word_t gamma1_p2, br_word_t gamma2_p2) {
  bn256_Fp2_felem_copy(out, x);
  bn256_Fp2_mul(out+64, x+64, gamma1_p2);
  bn256_Fp2_mul(out+128, x+128, gamma2_p2);
}

static void bn256_Fp12_frobenius(br_word_t out, br_word_t x, br_word_t gamma1, br_word_t gamma2, br_word_t w_frob_c1) {
  bn256_Fp6_frobenius(out, x, gamma1, gamma2);
  bn256_Fp6_frobenius(out+192, x+192, gamma1, gamma2);
  bn256_Fp6_mul_fp2(out+192, out+192, w_frob_c1);
}

static void bn256_Fp12_frobenius_p2(br_word_t out, br_word_t x, br_word_t gamma1_p2, br_word_t gamma2_p2, br_word_t w_frob_p2_c1) {
  bn256_Fp6_frobenius_p2(out, x, gamma1_p2, gamma2_p2);
  bn256_Fp6_frobenius_p2(out+192, x+192, gamma1_p2, gamma2_p2);
  bn256_Fp6_mul_fp2(out+192, out+192, w_frob_p2_c1);
}

static void bn256_Fp12_frobenius_p3(br_word_t out, br_word_t x, br_word_t gamma1, br_word_t gamma2, br_word_t gamma1_p2, br_word_t gamma2_p2, br_word_t w_frob_c1, br_word_t w_frob_p2_c1) {
  br_word_t tmp;
  uint8_t _br_stackalloc_tmp[0x180] = {0}; tmp = (br_word_t)&_br_stackalloc_tmp;
  bn256_Fp6_frobenius_p2(tmp, x, gamma1_p2, gamma2_p2);
  bn256_Fp6_frobenius_p2(tmp+192, x+192, gamma1_p2, gamma2_p2);
  bn256_Fp6_mul_fp2(tmp+192, tmp+192, w_frob_p2_c1);
  bn256_Fp6_frobenius(out, tmp, gamma1, gamma2);
  bn256_Fp6_frobenius(out+192, tmp+192, gamma1, gamma2);
  bn256_Fp6_mul_fp2(out+192, out+192, w_frob_c1);
}

static void bn256_Fp2_mul_fp(br_word_t out, br_word_t x, br_word_t s) {
  bn256_mul(out, x, s);
  bn256_mul(out+32, x+32, s);
}

static void bn256_make_line(br_word_t out, br_word_t lam, br_word_t x_t, br_word_t y_t, br_word_t x_p, br_word_t y_p) {
  br_word_t tmp;
  uint8_t _br_stackalloc_tmp[64] = {0}; tmp = (br_word_t)&_br_stackalloc_tmp;
  bn256_Fp2_mul(out, lam, x_t);
  bn256_Fp2_sub(out, out, y_t);
  bn256_Fp2_mul_fp(tmp, lam, x_p);
  bn256_Fp2_opp(out+64, tmp);
  bn256_from_word(out+128, (br_word_t)0);
  bn256_from_word((out+128)+32, (br_word_t)0);
  bn256_from_word(out+192, (br_word_t)0);
  bn256_from_word((out+192)+32, (br_word_t)0);
  bn256_felem_copy((out+192)+64, y_p);
  bn256_from_word(((out+192)+64)+32, (br_word_t)0);
  bn256_from_word((out+192)+128, (br_word_t)0);
  bn256_from_word(((out+192)+128)+32, (br_word_t)0);
}

static void bn256_load_gamma1_p2(br_word_t out) {
  _br_store(out, (br_word_t)0x12d3cef5e1ada57d);
  _br_store(out+8, (br_word_t)0xe2eca1463753babb);
  _br_store(out+16, (br_word_t)0xca41e40ddccf750);
  _br_store(out+24, (br_word_t)0x551337060397e04c);
  _br_store(out+32, (br_word_t)0);
  _br_store(out+40, (br_word_t)0);
  _br_store(out+48, (br_word_t)0);
  _br_store(out+56, (br_word_t)0);
}

static void bn256_load_gamma2_p2(br_word_t out) {
  _br_store(out, (br_word_t)0x3642364f386c1db8);
  _br_store(out+8, (br_word_t)0xe825f92d2acd661f);
  _br_store(out+16, (br_word_t)0xf2aba7e846c19d14);
  _br_store(out+24, (br_word_t)0x5a0bcea3dc52b7a0);
  _br_store(out+32, (br_word_t)0);
  _br_store(out+40, (br_word_t)0);
  _br_store(out+48, (br_word_t)0);
  _br_store(out+56, (br_word_t)0);
}

static void bn256_load_w_frob_p2_c1(br_word_t out) {
  _br_store(out, (br_word_t)0xe21a761d259c78af);
  _br_store(out+8, (br_word_t)0x6358fa3f5e84f7e );
  _br_store(out+16, (br_word_t)0xb7c444d01ac33f0d);
  _br_store(out+24, (br_word_t)0x35a9333f6e50d058);
  _br_store(out+32, (br_word_t)0);
  _br_store(out+40, (br_word_t)0);
  _br_store(out+48, (br_word_t)0);
  _br_store(out+56, (br_word_t)0);
}

static void bn256_load_gamma1(br_word_t out) {
  _br_store(out, (br_word_t)0xf8606916d3816f2c);
  _br_store(out+8, (br_word_t)0x1e5c0d7926de927e );
  _br_store(out+16, (br_word_t)0xbc45f3946d81185e );
  _br_store(out+24, (br_word_t)0x80752a25aa738091);
  _br_store(out+32, (br_word_t)0x4f59e37c01832e57);
  _br_store(out+40, (br_word_t)0xae6be39ac2bbbfe4);
  _br_store(out+48, (br_word_t)0xe04ea1bb697512f8);
  _br_store(out+56, (br_word_t)0x3097caa8fc40e10e );
}

static void bn256_load_gamma2(br_word_t out) {
  _br_store(out, (br_word_t)0x4d2ea218872f3d2c);
  _br_store(out+8, (br_word_t)0x2fcb27fc4abe7b69);
  _br_store(out+16, (br_word_t)0xd31d972f0e88ced9);
  _br_store(out+24, (br_word_t)0x53adc04a00a73b15);
  _br_store(out+32, (br_word_t)0x51678e7469b3c52a);
  _br_store(out+40, (br_word_t)0x4fb98f8b13319fc9);
  _br_store(out+48, (br_word_t)0x29b2254db3f1df75);
  _br_store(out+56, (br_word_t)0x1c044935a3d22fb2);
}

static void bn256_load_w_frob_c1(br_word_t out) {
  _br_store(out, (br_word_t)0x7407634dd9cca958);
  _br_store(out+8, (br_word_t)0x36d5bd6c7afb8f26);
  _br_store(out+16, (br_word_t)0xf4b1c32cebd880fa);
  _br_store(out+24, (br_word_t)0x6aa7869306f455f);
  _br_store(out+32, (br_word_t)0x25af52988477cdb7);
  _br_store(out+40, (br_word_t)0x3d81a455ddced86a);
  _br_store(out+48, (br_word_t)0x227d012e872c2431);
  _br_store(out+56, (br_word_t)0x179198d3ea65d05);
}

static void bn256_Fp12_pow_u(br_word_t out, br_word_t base) {
  br_word_t i, bit, result;
  uint8_t _br_stackalloc_result[0x180] = {0}; result = (br_word_t)&_br_stackalloc_result;
  bn256_Fp12_felem_copy(result, base);
  i = (br_word_t)62;
  while (i) {
    i = i-1;
    bn256_Fp12_square(result, result);
    bit = ((br_word_t)0x5a76ae9aec588301>>(i&(sizeof(br_word_t)*8-1)))&1;
    if (bit) {
      bn256_Fp12_mul(result, result, base);
    } else {
      /*skip*/
    }
  }
  bn256_Fp12_felem_copy(out, result);
}

static void bn256_final_exp_hard_dsd(br_word_t out, br_word_t f) {
  br_word_t gamma1, gamma2, w_frob_c1, t3, t1, t0, t2;
  uint8_t _br_stackalloc_t0[0x180] = {0}; t0 = (br_word_t)&_br_stackalloc_t0;
  uint8_t _br_stackalloc_t1[0x180] = {0}; t1 = (br_word_t)&_br_stackalloc_t1;
  uint8_t _br_stackalloc_t2[0x180] = {0}; t2 = (br_word_t)&_br_stackalloc_t2;
  uint8_t _br_stackalloc_t3[0x180] = {0}; t3 = (br_word_t)&_br_stackalloc_t3;
  uint8_t _br_stackalloc_gamma1[64] = {0}; gamma1 = (br_word_t)&_br_stackalloc_gamma1;
  uint8_t _br_stackalloc_gamma2[64] = {0}; gamma2 = (br_word_t)&_br_stackalloc_gamma2;
  uint8_t _br_stackalloc_w_frob_c1[64] = {0}; w_frob_c1 = (br_word_t)&_br_stackalloc_w_frob_c1;
  bn256_load_gamma1(gamma1);
  bn256_load_gamma2(gamma2);
  bn256_load_w_frob_c1(w_frob_c1);
  bn256_Fp12_pow_u(t0, f);
  bn256_Fp12_pow_u(t1, t0);
  bn256_Fp12_pow_u(t2, t1);
  bn256_Fp12_frobenius(t3, t2, gamma1, gamma2, w_frob_c1);
  bn256_Fp12_mul(t2, t2, t3);
  bn256_Fp12_conjugate(t2, t2);
  bn256_Fp12_square(out, t2);
  bn256_Fp12_frobenius(t2, t1, gamma1, gamma2, w_frob_c1);
  bn256_Fp12_mul(t3, t0, t2);
  bn256_Fp12_conjugate(t3, t3);
  bn256_Fp12_mul(out, out, t3);
  bn256_Fp12_conjugate(t3, t1);
  bn256_Fp12_mul(out, out, t3);
  bn256_Fp12_frobenius(t1, t0, gamma1, gamma2, w_frob_c1);
  bn256_Fp12_conjugate(t1, t1);
  bn256_Fp12_mul(t0, out, t1);
  bn256_Fp12_mul(t0, t0, t3);
  bn256_Fp12_frobenius(t1, t2, gamma1, gamma2, w_frob_c1);
  bn256_Fp12_mul(out, out, t1);
  bn256_Fp12_square(t1, t0);
  bn256_Fp12_mul(t1, t1, out);
  bn256_Fp12_square(t1, t1);
  bn256_Fp12_frobenius(t0, f, gamma1, gamma2, w_frob_c1);
  bn256_Fp12_frobenius(t2, t0, gamma1, gamma2, w_frob_c1);
  bn256_Fp12_frobenius(t3, t2, gamma1, gamma2, w_frob_c1);
  bn256_Fp12_mul(t0, t0, t2);
  bn256_Fp12_mul(t0, t0, t3);
  bn256_Fp12_mul(t2, t1, t0);
  bn256_Fp12_conjugate(t0, f);
  bn256_Fp12_mul(t0, t1, t0);
  bn256_Fp12_square(t0, t0);
  bn256_Fp12_mul(out, t0, t2);
}

static void bn256_final_exp_dsd(br_word_t out, br_word_t f, br_word_t gamma1_p2, br_word_t gamma2_p2, br_word_t w_frob_p2_c1) {
  br_word_t tmp, result;
  uint8_t _br_stackalloc_result[0x180] = {0}; result = (br_word_t)&_br_stackalloc_result;
  uint8_t _br_stackalloc_tmp[0x180] = {0}; tmp = (br_word_t)&_br_stackalloc_tmp;
  bn256_Fp12_conjugate(result, f);
  bn256_Fp12_inv(tmp, f);
  bn256_Fp12_mul(result, result, tmp);
  bn256_Fp12_frobenius_p2(tmp, result, gamma1_p2, gamma2_p2, w_frob_p2_c1);
  bn256_Fp12_mul(result, tmp, result);
  bn256_final_exp_hard_dsd(out, result);
}

static void bn256_miller_loop(br_word_t out, br_word_t p_x, br_word_t p_y, br_word_t q_x, br_word_t q_y) {
  br_word_t u6p2, word, i, bit, line, lambda, tmp1, t_y, t_x, tmp2, f;
  uint8_t _br_stackalloc_f[0x180] = {0}; f = (br_word_t)&_br_stackalloc_f;
  uint8_t _br_stackalloc_t_x[64] = {0}; t_x = (br_word_t)&_br_stackalloc_t_x;
  uint8_t _br_stackalloc_t_y[64] = {0}; t_y = (br_word_t)&_br_stackalloc_t_y;
  uint8_t _br_stackalloc_lambda[64] = {0}; lambda = (br_word_t)&_br_stackalloc_lambda;
  uint8_t _br_stackalloc_tmp1[64] = {0}; tmp1 = (br_word_t)&_br_stackalloc_tmp1;
  uint8_t _br_stackalloc_tmp2[64] = {0}; tmp2 = (br_word_t)&_br_stackalloc_tmp2;
  uint8_t _br_stackalloc_line[0x180] = {0}; line = (br_word_t)&_br_stackalloc_line;
  uint8_t _br_stackalloc_u6p2[16] = {0}; u6p2 = (br_word_t)&_br_stackalloc_u6p2;
  bn256_from_word(f, (br_word_t)1);
  bn256_from_word(f+32, (br_word_t)0);
  bn256_from_word(f+64, (br_word_t)0);
  bn256_from_word((f+64)+32, (br_word_t)0);
  bn256_from_word(f+128, (br_word_t)0);
  bn256_from_word((f+128)+32, (br_word_t)0);
  bn256_from_word(f+192, (br_word_t)0);
  bn256_from_word((f+192)+32, (br_word_t)0);
  bn256_from_word((f+192)+64, (br_word_t)0);
  bn256_from_word(((f+192)+64)+32, (br_word_t)0);
  bn256_from_word((f+192)+128, (br_word_t)0);
  bn256_from_word(((f+192)+128)+32, (br_word_t)0);
  bn256_Fp2_felem_copy(t_x, q_x);
  bn256_Fp2_felem_copy(t_y, q_y);
  _br_store(u6p2, (br_word_t)0x1ec817a18a131208);
  _br_store(u6p2+8, (br_word_t)2);
  i = (br_word_t)65;
  while (i) {
    i = i-1;
    word = _br_load(u6p2+((i>>6)<<3));
    bit = (word>>((i&63)&(sizeof(br_word_t)*8-1)))&1;
    bn256_Fp2_square(tmp1, t_x);
    bn256_Fp2_add(lambda, tmp1, tmp1);
    bn256_Fp2_add(lambda, lambda, tmp1);
    bn256_Fp2_add(tmp1, t_y, t_y);
    bn256_Fp2_inv(tmp1, tmp1);
    bn256_Fp2_mul(lambda, lambda, tmp1);
    bn256_make_line(line, lambda, t_x, t_y, p_x, p_y);
    bn256_Fp12_square(f, f);
    bn256_Fp12_mul(f, f, line);
    bn256_Fp2_square(tmp1, lambda);
    bn256_Fp2_sub(tmp1, tmp1, t_x);
    bn256_Fp2_sub(tmp2, tmp1, t_x);
    bn256_Fp2_sub(tmp1, t_x, tmp2);
    bn256_Fp2_mul(tmp1, lambda, tmp1);
    bn256_Fp2_sub(t_y, tmp1, t_y);
    bn256_Fp2_felem_copy(t_x, tmp2);
    if (bit) {
      bn256_Fp2_sub(tmp1, q_y, t_y);
      bn256_Fp2_sub(tmp2, q_x, t_x);
      bn256_Fp2_inv(tmp2, tmp2);
      bn256_Fp2_mul(lambda, tmp1, tmp2);
      bn256_make_line(line, lambda, t_x, t_y, p_x, p_y);
      bn256_Fp12_mul(f, f, line);
      bn256_Fp2_square(tmp1, lambda);
      bn256_Fp2_sub(tmp1, tmp1, t_x);
      bn256_Fp2_sub(tmp2, tmp1, q_x);
      bn256_Fp2_sub(tmp1, t_x, tmp2);
      bn256_Fp2_mul(tmp1, lambda, tmp1);
      bn256_Fp2_sub(t_y, tmp1, t_y);
      bn256_Fp2_felem_copy(t_x, tmp2);
    } else {
      /*skip*/
    }
  }
  bn256_Fp12_felem_copy(out, f);
}

static void bn256_pairing_dsd(br_word_t out, br_word_t p_x, br_word_t p_y, br_word_t q_x, br_word_t q_y) {
  br_word_t tmp, gamma1_p2, gamma2_p2, w_frob_p2_c1;
  uint8_t _br_stackalloc_tmp[0x180] = {0}; tmp = (br_word_t)&_br_stackalloc_tmp;
  uint8_t _br_stackalloc_gamma1_p2[64] = {0}; gamma1_p2 = (br_word_t)&_br_stackalloc_gamma1_p2;
  uint8_t _br_stackalloc_gamma2_p2[64] = {0}; gamma2_p2 = (br_word_t)&_br_stackalloc_gamma2_p2;
  uint8_t _br_stackalloc_w_frob_p2_c1[64] = {0}; w_frob_p2_c1 = (br_word_t)&_br_stackalloc_w_frob_p2_c1;
  bn256_load_gamma1_p2(gamma1_p2);
  bn256_load_gamma2_p2(gamma2_p2);
  bn256_load_w_frob_p2_c1(w_frob_p2_c1);
  bn256_miller_loop(tmp, p_x, p_y, q_x, q_y);
  bn256_final_exp_dsd(out, tmp, gamma1_p2, gamma2_p2, w_frob_p2_c1);
}
"
     : string
