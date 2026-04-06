/* Full tower A/B: bedrock2 C vs hand-written asm at every level */
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
typedef uintptr_t br_word_t;

#include "bls24_509_pairing.c"
void bls24_509_zero(br_word_t o){memset((void*)o,0,64);}
void bls24_509_one(br_word_t o){static const uint64_t R[8]={0xD50A57A3A6E01715ULL,0x4AB46410CFA0D504ULL,0x38E8E4D5D79D6774ULL,0x36CC2E2E7C7A56DCULL,0x6AFE0117020AA12EULL,0,0,0};memcpy((void*)o,R,64);}
void bls24_509_select_znz(br_word_t o,br_word_t c,br_word_t x,br_word_t y){uint64_t*oo=(uint64_t*)o,*a=(uint64_t*)x,*b=(uint64_t*)y;uint64_t m=-(uint64_t)(c!=0);for(int i=0;i<8;i++)oo[i]=(a[i]&~m)|(b[i]&m);}
void bls24_509_from_word(br_word_t o,br_word_t w){bls24_509_zero(o);if(w==1)bls24_509_one(o);}
void bls24_Fp4_inv(br_word_t o,br_word_t x){memcpy((void*)o,(void*)x,256);}
void bls24_Fp8_inv(br_word_t o,br_word_t x){memcpy((void*)o,(void*)x,512);}

extern void bls24_Fp2_mul_asm(br_word_t,br_word_t,br_word_t);
extern void bls24_Fp2_square_asm(br_word_t,br_word_t);
extern void bls24_Fp4_mul_asm(br_word_t,br_word_t,br_word_t);
extern void bls24_Fp4_square_asm(br_word_t,br_word_t);
extern void bls24_Fp8_mul_asm(br_word_t,br_word_t,br_word_t);
extern void bls24_Fp8_square_asm(br_word_t,br_word_t);
extern void bls24_Fp24_mul_asm(br_word_t,br_word_t,br_word_t);

static double get_ns(void){struct timespec ts;clock_gettime(CLOCK_MONOTONIC,&ts);return ts.tv_sec*1e9+ts.tv_nsec;}

int main(void) {
    uint8_t __attribute__((aligned(64))) a[1536]={0},b[1536]={0},c[1536]={0},d[1536]={0};
    br_word_t ap=(br_word_t)a,bp=(br_word_t)b,cp=(br_word_t)c,dp=(br_word_t)d;
    ((uint64_t*)a)[0]=7;((uint64_t*)a)[8]=3;((uint64_t*)a)[16]=11;((uint64_t*)a)[24]=2;
    ((uint64_t*)b)[0]=13;((uint64_t*)b)[8]=5;((uint64_t*)b)[16]=17;((uint64_t*)b)[24]=19;

    printf("=== Tower A/B: bedrock2 C vs hand-written asm ===\n\n");

    /* Correctness checks */
    int ok = 1;
    bls24_Fp2_mul(cp,ap,bp); bls24_Fp2_mul_asm(dp,ap,bp);
    if(memcmp(c,d,128)){printf("Fp2_mul: FAIL\n");ok=0;} else printf("Fp2_mul: PASS\n");
    bls24_Fp4_mul(cp,ap,bp); bls24_Fp4_mul_asm(dp,ap,bp);
    if(memcmp(c,d,256)){printf("Fp4_mul: FAIL\n");ok=0;} else printf("Fp4_mul: PASS\n");
    bls24_Fp8_mul(cp,ap,bp); bls24_Fp8_mul_asm(dp,ap,bp);
    if(memcmp(c,d,512)){printf("Fp8_mul: FAIL\n");ok=0;} else printf("Fp8_mul: PASS\n");
    bls24_Fp24_mul(cp,ap,bp); bls24_Fp24_mul_asm(dp,ap,bp);
    if(memcmp(c,d,1536)){printf("Fp24_mul: FAIL\n");ok=0;} else printf("Fp24_mul: PASS\n");
    if(!ok){printf("\nCorrectness failure — aborting\n");return 1;}
    printf("\n");

    /* Interleaved benchmarks */
    for(int round=0;round<3;round++){
        printf("Round %d:\n",round+1);

        #define AB(name,sz,br2call,asmcall,N) { \
            for(int w=0;w<100;w++){br2call;} \
            double s1=get_ns();for(int i=0;i<N;i++){br2call;}double e1=get_ns(); \
            for(int w=0;w<100;w++){asmcall;} \
            double s2=get_ns();for(int i=0;i<N;i++){asmcall;}double e2=get_ns(); \
            printf("  %-12s br2=%7.0f ns  asm=%7.0f ns  speedup=%.2fx\n", \
                   name,(e1-s1)/N,(e2-s2)/N,(e1-s1)/(e2-s2)); }

        AB("Fp2_mul",128, bls24_Fp2_mul(cp,ap,bp), bls24_Fp2_mul_asm(dp,ap,bp), 300000)
        AB("Fp4_mul",256, bls24_Fp4_mul(cp,ap,bp), bls24_Fp4_mul_asm(dp,ap,bp), 100000)
        AB("Fp8_mul",512, bls24_Fp8_mul(cp,ap,bp), bls24_Fp8_mul_asm(dp,ap,bp), 50000)
        AB("Fp24_mul",1536, bls24_Fp24_mul(cp,ap,bp), bls24_Fp24_mul_asm(dp,ap,bp), 10000)
        printf("\n");
    }
    return 0;
}
