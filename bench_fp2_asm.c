/* A/B: bedrock2 Fp2_mul vs hand-written asm Fp2_mul */
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
typedef uintptr_t br_word_t;

/* Include extracted code for bedrock2 versions */
#include "bls24_509_pairing.c"

/* Stubs */
void bls24_509_zero(br_word_t o){memset((void*)o,0,64);}
void bls24_509_one(br_word_t o){static const uint64_t R[8]={0xD50A57A3A6E01715ULL,0x4AB46410CFA0D504ULL,0x38E8E4D5D79D6774ULL,0x36CC2E2E7C7A56DCULL,0x6AFE0117020AA12EULL,0,0,0};memcpy((void*)o,R,64);}
void bls24_509_select_znz(br_word_t o,br_word_t c,br_word_t x,br_word_t y){uint64_t*oo=(uint64_t*)o,*a=(uint64_t*)x,*b=(uint64_t*)y;uint64_t m=-(uint64_t)(c!=0);for(int i=0;i<8;i++)oo[i]=(a[i]&~m)|(b[i]&m);}
void bls24_509_from_word(br_word_t o,br_word_t w){bls24_509_zero(o);if(w==1)bls24_509_one(o);}

/* Extern: hand-written asm Fp2 mul */
extern void bls24_Fp2_mul_asm(br_word_t out, br_word_t inx, br_word_t iny);

/* Also need CryptOpt mul for the asm version */
extern void fiat_bls24_509_p_mul(uint64_t*, const uint64_t*, const uint64_t*);

static double get_ns(void){struct timespec ts;clock_gettime(CLOCK_MONOTONIC,&ts);return ts.tv_sec*1e9+ts.tv_nsec;}

int main(void) {
    uint8_t __attribute__((aligned(64))) a[128]={0},b[128]={0},c[128]={0},d[128]={0};
    ((uint64_t*)a)[0]=7;((uint64_t*)a)[8]=3;
    ((uint64_t*)b)[0]=13;((uint64_t*)b)[8]=5;

    int N = 500000;

    /* Warmup + verify correctness */
    bls24_Fp2_mul((br_word_t)c, (br_word_t)a, (br_word_t)b);
    bls24_Fp2_mul_asm((br_word_t)d, (br_word_t)a, (br_word_t)b);
    if (memcmp(c, d, 128) == 0) {
        printf("Correctness: PASS (asm matches bedrock2)\n\n");
    } else {
        printf("Correctness: FAIL!\n");
        printf("  bedrock2 c0[0] = 0x%lx\n", ((uint64_t*)c)[0]);
        printf("  asm      c0[0] = 0x%lx\n", ((uint64_t*)d)[0]);
        /* Continue anyway to get timing */
    }

    /* Interleaved benchmark */
    for (int round = 0; round < 3; round++) {
        for(int w=0;w<200;w++) bls24_Fp2_mul((br_word_t)c,(br_word_t)a,(br_word_t)b);
        double s1=get_ns();
        for(int i=0;i<N;i++) bls24_Fp2_mul((br_word_t)c,(br_word_t)a,(br_word_t)b);
        double e1=get_ns();

        for(int w=0;w<200;w++) bls24_Fp2_mul_asm((br_word_t)d,(br_word_t)a,(br_word_t)b);
        double s2=get_ns();
        for(int i=0;i<N;i++) bls24_Fp2_mul_asm((br_word_t)d,(br_word_t)a,(br_word_t)b);
        double e2=get_ns();

        printf("Round %d: bedrock2=%.1f ns  asm=%.1f ns  speedup=%.2fx\n",
               round+1, (e1-s1)/N, (e2-s2)/N, (e1-s1)/(e2-s2));
    }
    return 0;
}
/* Inv stubs (not needed for Fp2 benchmark) */
void bls24_Fp4_inv(br_word_t o,br_word_t x){memcpy((void*)o,(void*)x,256);}
void bls24_Fp8_inv(br_word_t o,br_word_t x){memcpy((void*)o,(void*)x,512);}
