// Compile with: clang maxRelErr.c -O -lm
// Adding -m32 does not affect the results either
//
// Expected output:
// ===============
// arch: 64-bit
// magic: 0x5F3759DF
// worst: 0x016EB3C0 (0.000000000000)
// fSqrt: 0x20773327 (0.000000000000)
// fFast: 0x5E84530F (4767490664373944320.000000000000)
// maxRelErr: 0x3AE5B000 (0.0017523765563964844)
#include <stdint.h>
#include <math.h>
#include <stdio.h>
#include <assert.h>

const int32_t magic = 0x5f3759df;

float Q_rsqrt(float f) {
    int32_t b = *(int32_t*)&f;
    b = magic - (b >> 1); // The actual bit-level hack
    float res = *(float*)&b;

    // Run one iteration of Newton's method to improve precision
    float fHalf = f * 0.5f;
    return res * (1.5f - fHalf * res * res);
}

float relErr(float fSqrt, float fFast) {
    return fabs(1.0f - fFast*fSqrt);
}

float findWorst() {
    float curMax = 0, worstF = 0;
    union {float f; uint32_t b;} u = {0};
    do {
        // Hack doesn't really work for all floats, so we filter
        if(isnormal(u.f) && u.f >= 0.0f) {
            float fSqrt = sqrt(u.f);
            float fFast = Q_rsqrt(u.f);
            float curRelErr = relErr(fSqrt, fFast);
            if(curRelErr > curMax) {
                curMax = curRelErr;
                worstF = u.f;
            }
        }
    } while(++u.b != 0);
    return worstF;
}

int main() {
    printf("arch: %zu-bit\nmagic: 0x%08X\n", sizeof(size_t)*8, magic);
    float worstF = findWorst();

    float fSqrt = sqrt(worstF);
    float fFast = Q_rsqrt(worstF);
    float maxRelErr = relErr(fSqrt, fFast);

    printf("worst: 0x%08X (%.12f)\n", *(uint32_t*)&worstF ,worstF);
    printf("fSqrt: 0x%08X (%.12f)\n", *(uint32_t*)&fSqrt, fSqrt);
    printf("fFast: 0x%08X (%.12f)\n", *(uint32_t*)&fFast, fFast);
    printf("maxRelErr: 0x%08X (%.19f)\n", *(uint32_t*)&maxRelErr, maxRelErr);
}
