/* Bridge: bedrock2 calls bls24_509_mul(uintptr_t, uintptr_t, uintptr_t)
   CryptOpt provides fiat_bls24_509_p_mul(uint64_t*, uint64_t*, uint64_t*)
   Same calling convention on x86-64 (first 3 args in rdi, rsi, rdx). */
#include <stdint.h>
extern void fiat_bls24_509_p_mul(uint64_t*, const uint64_t*, const uint64_t*);
extern void fiat_bls24_509_p_square(uint64_t*, const uint64_t*);

void bls24_509_mul(uintptr_t out, uintptr_t in0, uintptr_t in1) {
    fiat_bls24_509_p_mul((uint64_t*)out, (const uint64_t*)in0, (const uint64_t*)in1);
}

#ifdef HAS_CRYPTOPT_SQR
void bls24_509_square(uintptr_t out, uintptr_t in0) {
    fiat_bls24_509_p_square((uint64_t*)out, (const uint64_t*)in0);
}
#endif
