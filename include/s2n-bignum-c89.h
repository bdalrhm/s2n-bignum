/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "LICENSE" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */

/* ----------------------------------------------------------------------------
 * C prototypes for s2n-bignum functions, so you can use them in C programs via
 *
 *  #include "s2n-bignum-c89.h"
 *
 * The functions are listed in alphabetical order with a brief description
 * in comments for each one. For more detailed documentation see the comment
 * banner at the top of the corresponding assembly (.S) file, and
 * for the last word in what properties it satisfies see the spec in the
 * formal proof (the .ml file in the architecture-specific directory).
 * ----------------------------------------------------------------------------
 */

/*  Add, z := x + y */
/*  Inputs x[m], y[n]; outputs function return (carry-out) and z[p] */
extern uint64_t bignum_add (uint64_t p, uint64_t *z, uint64_t m, uint64_t *x, uint64_t n, uint64_t *y);

/*  Add modulo p_256, z := (x + y) mod p_256, assuming x and y reduced */
/*  Inputs x[4], y[4]; output z[4] */
extern void bignum_add_p256 (uint64_t z[4], uint64_t x[4], uint64_t y[4]);

/*  Add modulo p_256k1, z := (x + y) mod p_256k1, assuming x and y reduced */
/*  Inputs x[4], y[4]; output z[4] */
extern void bignum_add_p256k1 (uint64_t z[4], uint64_t x[4], uint64_t y[4]);

/*  Add modulo p_384, z := (x + y) mod p_384, assuming x and y reduced */
/*  Inputs x[6], y[6]; output z[6] */
extern void bignum_add_p384 (uint64_t z[6], uint64_t x[6], uint64_t y[6]);

/*  Add modulo p_521, z := (x + y) mod p_521, assuming x and y reduced */
/*  Inputs x[9], y[9]; output z[9] */
extern void bignum_add_p521 (uint64_t z[9], uint64_t x[9], uint64_t y[9]);

/*  Compute "amontification" constant z :== 2^{128k} (congruent mod m) */
/*  Input m[k]; output z[k]; temporary buffer t[>=k] */
extern void bignum_amontifier (uint64_t k, uint64_t *z, uint64_t *m, uint64_t *t);

/*  Almost-Montgomery multiply, z :== (x * y / 2^{64k}) (congruent mod m) */
/*  Inputs x[k], y[k], m[k]; output z[k] */
extern void bignum_amontmul (uint64_t k, uint64_t *z, uint64_t *x, uint64_t *y, uint64_t *m);

/*  Almost-Montgomery reduce, z :== (x' / 2^{64p}) (congruent mod m) */
/*  Inputs x[n], m[k], p; output z[k] */
extern void bignum_amontredc (uint64_t k, uint64_t *z, uint64_t n, uint64_t *x, uint64_t *m, uint64_t p);

/*  Almost-Montgomery square, z :== (x^2 / 2^{64k}) (congruent mod m) */
/*  Inputs x[k], y[k]; output z[k] */
extern void bignum_amontsqr (uint64_t k, uint64_t *z, uint64_t *x, uint64_t *y);

/*  Convert 4-digit (256-bit) bignum to/from big-endian form */
/*  Input x[4]; output z[4] */
extern void bignum_bigendian_4 (uint64_t z[4], uint64_t x[4]);

/*  Convert 6-digit (384-bit) bignum to/from big-endian form */
/*  Input x[6]; output z[6] */
extern void bignum_bigendian_6 (uint64_t z[6], uint64_t x[6]);

/*  Select bitfield starting at bit n with length l <= 64 */
/*  Inputs x[k], n, l; output function return */
extern uint64_t bignum_bitfield (uint64_t k, uint64_t *x, uint64_t n, uint64_t l);

/*  Return size of bignum in bits */
/*  Input x[k]; output function return */
extern uint64_t bignum_bitsize (uint64_t k, uint64_t *x);

/*  Divide by a single (nonzero) word, z := x / m and return x mod m */
/*  Inputs x[n], m; outputs function return (remainder) and z[k] */
extern uint64_t bignum_cdiv (uint64_t k, uint64_t *z, uint64_t n, uint64_t *x, uint64_t m);

/*  Divide by a single word, z := x / m when known to be exact */
/*  Inputs x[n], m; output z[k] */
extern void bignum_cdiv_exact (uint64_t k, uint64_t *z, uint64_t n, uint64_t *x, uint64_t m);

/*  Count leading zero digits (64-bit words) */
/*  Input x[k]; output function return */
extern uint64_t bignum_cld (uint64_t k, uint64_t *x);

/*  Connt leading zero bits */
/*  Input x[k]; output function return */
extern uint64_t bignum_clz (uint64_t k, uint64_t *x);

/*  Multiply-add with single-word multiplier, z := z + c * y */
/*  Inputs c, y[n]; outputs function return (carry-out) and z[k] */
extern uint64_t bignum_cmadd (uint64_t k, uint64_t *z, uint64_t c, uint64_t n, uint64_t *y);

/*  Negated multiply-add with single-word multiplier, z := z - c * y */
/*  Inputs c, y[n]; outputs function return (negative carry-out) and z[k] */
extern uint64_t bignum_cmnegadd (uint64_t k, uint64_t *z, uint64_t c, uint64_t n, uint64_t *y);

/*  Find modulus of bignum w.r.t. single nonzero word m, returning x mod m */
/*  Input x[k], m; output function return */
extern uint64_t bignum_cmod (uint64_t k, uint64_t *x, uint64_t m);

/*  Multiply by a single word, z := c * y */
/*  Inputs c, y[n]; outputs function return (carry-out) and z[k] */
extern uint64_t bignum_cmul (uint64_t k, uint64_t *z, uint64_t c, uint64_t n, uint64_t *y);

/*  Multiply by a single word modulo p_256, z := (c * x) mod p_256, assuming x reduced */
/*  Inputs c, x[4]; output z[4] */
extern void bignum_cmul_p256 (uint64_t z[4], uint64_t c, uint64_t x[4]);

/*  Multiply by a single word modulo p_256k1, z := (c * x) mod p_256k1, assuming x reduced */
/*  Inputs c, x[4]; output z[4] */
extern void bignum_cmul_p256k1 (uint64_t z[4], uint64_t c, uint64_t x[4]);

/*  Multiply by a single word modulo p_384, z := (c * x) mod p_384, assuming x reduced */
/*  Inputs c, x[6]; output z[6] */
extern void bignum_cmul_p384 (uint64_t z[6], uint64_t c, uint64_t x[6]);

/*  Multiply by a single word modulo p_521, z := (c * x) mod p_521, assuming x reduced */
/*  Inputs c, x[9]; output z[9] */
extern void bignum_cmul_p521 (uint64_t z[9], uint64_t c, uint64_t x[9]);

/*  Test bignums for coprimality, gcd(x,y) = 1 */
/*  Inputs x[m], y[n]; output function return; temporary buffer t[>=2*max(m,n)] */
extern uint64_t bignum_coprime (uint64_t m, uint64_t *x, uint64_t n, uint64_t *y, uint64_t *t);

/*  Copy bignum with zero-extension or truncation, z := x */
/*  Input x[n]; output z[k] */
extern void bignum_copy (uint64_t k, uint64_t *z, uint64_t n, uint64_t *x);

/*  Count trailing zero digits (64-bit words) */
/*  Input x[k]; output function return */
extern uint64_t bignum_ctd (uint64_t k, uint64_t *x);

/*  Count trailing zero bits */
/*  Input x[k]; output function return */
extern uint64_t bignum_ctz (uint64_t k, uint64_t *x);

/*  Convert from almost-Montgomery form, z := (x / 2^256) mod p_256 */
/*  Input x[4]; output z[4] */
extern void bignum_deamont_p256 (uint64_t z[4], uint64_t x[4]);

/*  Convert from almost-Montgomery form, z := (x / 2^256) mod p_256k1 */
/*  Input x[4]; output z[4] */
extern void bignum_deamont_p256k1 (uint64_t z[4], uint64_t x[4]);

/*  Convert from almost-Montgomery form, z := (x / 2^384) mod p_384 */
/*  Input x[6]; output z[6] */
extern void bignum_deamont_p384 (uint64_t z[6], uint64_t x[6]);

/*  Convert from almost-Montgomery form z := (x / 2^576) mod p_521 */
/*  Input x[9]; output z[9] */
extern void bignum_deamont_p521 (uint64_t z[9], uint64_t x[9]);

/*  Convert from (almost-)Montgomery form z := (x / 2^{64k}) mod m */
/*  Inputs x[k], m[k]; output z[k] */
extern void bignum_demont (uint64_t k, uint64_t *z, uint64_t *x, uint64_t *m);

/*  Convert from Montgomery form z := (x / 2^256) mod p_256, assuming x reduced */
/*  Input x[4]; output z[4] */
extern void bignum_demont_p256 (uint64_t z[4], uint64_t x[4]);

/*  Convert from Montgomery form z := (x / 2^256) mod p_256k1, assuming x reduced */
/*  Input x[4]; output z[4] */
extern void bignum_demont_p256k1 (uint64_t z[4], uint64_t x[4]);

/*  Convert from Montgomery form z := (x / 2^384) mod p_384, assuming x reduced */
/*  Input x[6]; output z[6] */
extern void bignum_demont_p384 (uint64_t z[6], uint64_t x[6]);

/*  Convert from Montgomery form z := (x / 2^576) mod p_521, assuming x reduced */
/*  Input x[9]; output z[9] */
extern void bignum_demont_p521 (uint64_t z[9], uint64_t x[9]);

/*  Select digit x[n] */
/*  Inputs x[k], n; output function return */
extern uint64_t bignum_digit (uint64_t k, uint64_t *x, uint64_t n);

/*  Return size of bignum in digits (64-bit word) */
/*  Input x[k]; output function return */
extern uint64_t bignum_digitsize (uint64_t k, uint64_t *x);

/*  Divide bignum by 10: z' := z div 10, returning remainder z mod 10 */
/*  Inputs z[k]; outputs function return (remainder) and z[k] */
extern uint64_t bignum_divmod10 (uint64_t k, uint64_t *z);

/*  Double modulo p_256, z := (2 * x) mod p_256, assuming x reduced */
/*  Input x[4]; output z[4] */
extern void bignum_double_p256 (uint64_t z[4], uint64_t x[4]);

/*  Double modulo p_256k1, z := (2 * x) mod p_256k1, assuming x reduced */
/*  Input x[4]; output z[4] */
extern void bignum_double_p256k1 (uint64_t z[4], uint64_t x[4]);

/*  Double modulo p_384, z := (2 * x) mod p_384, assuming x reduced */
/*  Input x[6]; output z[6] */
extern void bignum_double_p384 (uint64_t z[6], uint64_t x[6]);

/*  Double modulo p_521, z := (2 * x) mod p_521, assuming x reduced */
/*  Input x[9]; output z[9] */
extern void bignum_double_p521 (uint64_t z[9], uint64_t x[9]);

/*  Extended Montgomery reduce, returning results in input-output buffer */
/*  Inputs z[2*k], m[k], w; outputs function return (extra result bit) and z[2*k] */
extern uint64_t bignum_emontredc (uint64_t k, uint64_t *z, uint64_t *m, uint64_t w);

/*  Extended Montgomery reduce in 8-digit blocks, results in input-output buffer */
/*  Inputs z[2*k], m[k], w; outputs function return (extra result bit) and z[2*k] */
extern uint64_t bignum_emontredc_8n (uint64_t k, uint64_t *z, uint64_t *m, uint64_t w);

/*  Test bignums for equality, x = y */
/*  Inputs x[m], y[n]; output function return */
extern uint64_t bignum_eq (uint64_t m, uint64_t *x, uint64_t n, uint64_t *y);

/*  Test bignum for even-ness */
/*  Input x[k]; output function return */
extern uint64_t bignum_even (uint64_t k, uint64_t *x);

/*  Convert 4-digit (256-bit) bignum from big-endian bytes */
/*  Input x[32] (bytes); output z[4] */
extern void bignum_frombebytes_4 (uint64_t z[4], uint8_t x[32]);

/*  Convert 6-digit (384-bit) bignum from big-endian bytes */
/*  Input x[48] (bytes); output z[6] */
extern void bignum_frombebytes_6 (uint64_t z[6], uint8_t x[48]);

/*  Convert 4-digit (256-bit) bignum from little-endian bytes */
/*  Input x[32] (bytes); output z[4] */
extern void bignum_fromlebytes_4 (uint64_t z[4], uint8_t x[32]);

/*  Convert 6-digit (384-bit) bignum from little-endian bytes */
/*  Input x[48] (bytes); output z[6] */
extern void bignum_fromlebytes_6 (uint64_t z[6], uint8_t x[48]);

/*  Compare bignums, x >= y */
/*  Inputs x[m], y[n]; output function return */
extern uint64_t bignum_ge (uint64_t m, uint64_t *x, uint64_t n, uint64_t *y);

/*  Compare bignums, x > y */
/*  Inputs x[m], y[n]; output function return */
extern uint64_t bignum_gt (uint64_t m, uint64_t *x, uint64_t n, uint64_t *y);

/*  Halve modulo p_256, z := (x / 2) mod p_256, assuming x reduced */
/*  Input x[4]; output z[4] */
extern void bignum_half_p256 (uint64_t z[4], uint64_t x[4]);

/*  Halve modulo p_256k1, z := (x / 2) mod p_256k1, assuming x reduced */
/*  Input x[4]; output z[4] */
extern void bignum_half_p256k1 (uint64_t z[4], uint64_t x[4]);

/*  Halve modulo p_384, z := (x / 2) mod p_384, assuming x reduced */
/*  Input x[6]; output z[6] */
extern void bignum_half_p384 (uint64_t z[6], uint64_t x[6]);

/*  Halve modulo p_521, z := (x / 2) mod p_521, assuming x reduced */
/*  Input x[9]; output z[9] */
extern void bignum_half_p521 (uint64_t z[9], uint64_t x[9]);

/*  Test bignum for zero-ness, x = 0 */
/*  Input x[k]; output function return */
extern uint64_t bignum_iszero (uint64_t k, uint64_t *x);

/*  Multiply z := x * y */
/*  Inputs x[16], y[16]; output z[32]; temporary buffer t[>=32] */
extern void bignum_kmul_16_32 (uint64_t z[32], uint64_t x[16], uint64_t y[16], uint64_t t[32]);

/*  Multiply z := x * y */
/*  Inputs x[32], y[32]; output z[64]; temporary buffer t[>=96] */
extern void bignum_kmul_32_64 (uint64_t z[64], uint64_t x[32], uint64_t y[32], uint64_t t[96]);

/*  Square, z := x^2 */
/*  Input x[16]; output z[32]; temporary buffer t[>=24] */
extern void bignum_ksqr_16_32 (uint64_t z[32], uint64_t x[16], uint64_t t[24]);

/*  Square, z := x^2 */
/*  Input x[32]; output z[64]; temporary buffer t[>=72] */
extern void bignum_ksqr_32_64 (uint64_t z[64], uint64_t x[32], uint64_t t[72]);

/*  Compare bignums, x <= y */
/*  Inputs x[m], y[n]; output function return */
extern uint64_t bignum_le (uint64_t m, uint64_t *x, uint64_t n, uint64_t *y);

/*  Convert 4-digit (256-bit) bignum to/from little-endian form */
/*  Input x[4]; output z[4] */
extern void bignum_littleendian_4 (uint64_t z[4], uint64_t x[4]);

/*  Convert 6-digit (384-bit) bignum to/from little-endian form */
/*  Input x[6]; output z[6] */
extern void bignum_littleendian_6 (uint64_t z[6], uint64_t x[6]);

/*  Compare bignums, x < y */
/*  Inputs x[m], y[n]; output function return */
extern uint64_t bignum_lt (uint64_t m, uint64_t *x, uint64_t n, uint64_t *y);

/*  Multiply-add, z := z + x * y */
/*  Inputs x[m], y[n]; outputs function return (carry-out) and z[k] */
extern uint64_t bignum_madd (uint64_t k, uint64_t *z, uint64_t m, uint64_t *x, uint64_t n, uint64_t *y);

/*  Reduce modulo group order, z := x mod n_256 */
/*  Input x[k]; output z[4] */
extern void bignum_mod_n256 (uint64_t z[4], uint64_t k, uint64_t *x);

/*  Reduce modulo group order, z := x mod n_256 */
/*  Input x[4]; output z[4] */
extern void bignum_mod_n256_4 (uint64_t z[4], uint64_t x[4]);

/*  Reduce modulo group order, z := x mod n_256k1 */
/*  Input x[4]; output z[4] */
extern void bignum_mod_n256k1_4 (uint64_t z[4], uint64_t x[4]);

/*  Reduce modulo group order, z := x mod n_384 */
/*  Input x[k]; output z[6] */
extern void bignum_mod_n384 (uint64_t z[6], uint64_t k, uint64_t *x);

/*  Reduce modulo group order, z := x mod n_384 */
/*  Input x[6]; output z[6] */
extern void bignum_mod_n384_6 (uint64_t z[6], uint64_t x[6]);

/*  Reduce modulo group order, z := x mod n_521 */
/*  Input x[9]; output z[9] */
extern void bignum_mod_n521_9 (uint64_t z[9], uint64_t x[9]);

/*  Reduce modulo field characteristic, z := x mod p_256 */
/*  Input x[k]; output z[4] */
extern void bignum_mod_p256 (uint64_t z[4], uint64_t k, uint64_t *x);

/*  Reduce modulo field characteristic, z := x mod p_256 */
/*  Input x[4]; output z[4] */
extern void bignum_mod_p256_4 (uint64_t z[4], uint64_t x[4]);

/*  Reduce modulo field characteristic, z := x mod p_256k1 */
/*  Input x[4]; output z[4] */
extern void bignum_mod_p256k1_4 (uint64_t z[4], uint64_t x[4]);

/*  Reduce modulo field characteristic, z := x mod p_384 */
/*  Input x[k]; output z[6] */
extern void bignum_mod_p384 (uint64_t z[6], uint64_t k, uint64_t *x);

/*  Reduce modulo field characteristic, z := x mod p_384 */
/*  Input x[6]; output z[6] */
extern void bignum_mod_p384_6 (uint64_t z[6], uint64_t x[6]);

/*  Reduce modulo field characteristic, z := x mod p_521 */
/*  Input x[9]; output z[9] */
extern void bignum_mod_p521_9 (uint64_t z[9], uint64_t x[9]);

/*  Add modulo m, z := (x + y) mod m, assuming x and y reduced */
/*  Inputs x[k], y[k], m[k]; output z[k] */
extern void bignum_modadd (uint64_t k, uint64_t *z, uint64_t *x, uint64_t *y, uint64_t *m);

/*  Double modulo m, z := (2 * x) mod m, assuming x reduced */
/*  Inputs x[k], m[k]; output z[k] */
extern void bignum_moddouble (uint64_t k, uint64_t *z, uint64_t *x, uint64_t *m);

/*  Compute "modification" constant z := 2^{64k} mod m */
/*  Input m[k]; output z[k]; temporary buffer t[>=k] */
extern void bignum_modifier (uint64_t k, uint64_t *z, uint64_t *m, uint64_t *t);

/*  Invert modulo m, z = (1/a) mod b, assuming b is an odd number > 1, a coprime to b */
/*  Inputs a[k], b[k]; output z[k]; temporary buffer t[>=3*k] */
extern void bignum_modinv (uint64_t k, uint64_t *z, uint64_t *a, uint64_t *b, uint64_t *t);

/*  Optionally negate modulo m, z := (-x) mod m (if p nonzero) or z := x (if p zero), assuming x reduced */
/*  Inputs p, x[k], m[k]; output z[k] */
extern void bignum_modoptneg (uint64_t k, uint64_t *z, uint64_t p, uint64_t *x, uint64_t *m);

/*  Subtract modulo m, z := (x - y) mod m, assuming x and y reduced */
/*  Inputs x[k], y[k], m[k]; output z[k] */
extern void bignum_modsub (uint64_t k, uint64_t *z, uint64_t *x, uint64_t *y, uint64_t *m);

/*  Compute "montification" constant z := 2^{128k} mod m */
/*  Input m[k]; output z[k]; temporary buffer t[>=k] */
extern void bignum_montifier (uint64_t k, uint64_t *z, uint64_t *m, uint64_t *t);

/*  Montgomery multiply, z := (x * y / 2^{64k}) mod m */
/*  Inputs x[k], y[k], m[k]; output z[k] */
extern void bignum_montmul (uint64_t k, uint64_t *z, uint64_t *x, uint64_t *y, uint64_t *m);

/*  Montgomery multiply, z := (x * y / 2^256) mod p_256 */
/*  Inputs x[4], y[4]; output z[4] */
extern void bignum_montmul_p256 (uint64_t z[4], uint64_t x[4], uint64_t y[4]);

/*  Montgomery multiply, z := (x * y / 2^256) mod p_256k1 */
/*  Inputs x[4], y[4]; output z[4] */
extern void bignum_montmul_p256k1 (uint64_t z[4], uint64_t x[4], uint64_t y[4]);

/*  Montgomery multiply, z := (x * y / 2^384) mod p_384 */
/*  Inputs x[6], y[6]; output z[6] */
extern void bignum_montmul_p384 (uint64_t z[6], uint64_t x[6], uint64_t y[6]);

/*  Montgomery multiply, z := (x * y / 2^576) mod p_521 */
/*  Inputs x[9], y[9]; output z[9] */
extern void bignum_montmul_p521 (uint64_t z[9], uint64_t x[9], uint64_t y[9]);

/*  Montgomery reduce, z := (x' / 2^{64p}) MOD m */
/*  Inputs x[n], m[k], p; output z[k] */
extern void bignum_montredc (uint64_t k, uint64_t *z, uint64_t n, uint64_t *x, uint64_t *m, uint64_t p);

/*  Montgomery square, z := (x^2 / 2^{64k}) mod m */
/*  Inputs x[k], y[k]; output z[k] */
extern void bignum_montsqr (uint64_t k, uint64_t *z, uint64_t *x, uint64_t *y);

/*  Montgomery square, z := (x^2 / 2^256) mod p_256 */
/*  Input x[4]; output z[4] */
extern void bignum_montsqr_p256 (uint64_t z[4], uint64_t x[4]);

/*  Montgomery square, z := (x^2 / 2^256) mod p_256k1 */
/*  Input x[4]; output z[4] */
extern void bignum_montsqr_p256k1 (uint64_t z[4], uint64_t x[4]);

/*  Montgomery square, z := (x^2 / 2^384) mod p_384 */
/*  Input x[6]; output z[6] */
extern void bignum_montsqr_p384 (uint64_t z[6], uint64_t x[6]);

/*  Montgomery square, z := (x^2 / 2^576) mod p_521 */
/*  Input x[9]; output z[9] */
extern void bignum_montsqr_p521 (uint64_t z[9], uint64_t x[9]);

/*  Multiply z := x * y */
/*  Inputs x[m], y[n]; output z[k] */
extern void bignum_mul (uint64_t k, uint64_t *z, uint64_t m, uint64_t *x, uint64_t n, uint64_t *y);

/*  Multiply z := x * y */
/*  Inputs x[4], y[4]; output z[8] */
extern void bignum_mul_4_8 (uint64_t z[8], uint64_t x[4], uint64_t y[4]);

/*  Multiply z := x * y */
/*  Inputs x[6], y[6]; output z[12] */
extern void bignum_mul_6_12 (uint64_t z[12], uint64_t x[6], uint64_t y[6]);

/*  Multiply z := x * y */
/*  Inputs x[8], y[8]; output z[16] */
extern void bignum_mul_8_16 (uint64_t z[16], uint64_t x[8], uint64_t y[8]);

/*  Multiply modulo p_256k1, z := (x * y) mod p_256k1 */
/*  Inputs x[4], y[4]; output z[4] */
extern void bignum_mul_p256k1 (uint64_t z[4], uint64_t x[4], uint64_t y[4]);

/*  Multiply modulo p_521, z := (x * y) mod p_521, assuming x and y reduced */
/*  Inputs x[9], y[9]; output z[9] */
extern void bignum_mul_p521 (uint64_t z[9], uint64_t x[9], uint64_t y[9]);

/*  Multiply bignum by 10 and add word: z := 10 * z + d */
/*  Inputs z[k], d; outputs function return (carry) and z[k] */
extern uint64_t bignum_muladd10 (uint64_t k, uint64_t *z, uint64_t d);

/*  Multiplex/select z := x (if p nonzero) or z := y (if p zero) */
/*  Inputs p, x[k], y[k]; output z[k] */
extern void bignum_mux (uint64_t p, uint64_t k, uint64_t *z, uint64_t *x, uint64_t *y);

/*  256-bit multiplex/select z := x (if p nonzero) or z := y (if p zero) */
/*  Inputs p, x[4], y[4]; output z[4] */
extern void bignum_mux_4 (uint64_t p, uint64_t z[4],uint64_t x[4], uint64_t y[4]);

/*  384-bit multiplex/select z := x (if p nonzero) or z := y (if p zero) */
/*  Inputs p, x[6], y[6]; output z[6] */
extern void bignum_mux_6 (uint64_t p, uint64_t z[6],uint64_t x[6], uint64_t y[6]);

/*  Select element from 16-element table, z := xs[k*i] */
/*  Inputs xs[16*k], i; output z[k] */
extern void bignum_mux16 (uint64_t k, uint64_t *z, uint64_t *xs, uint64_t i);

/*  Negate modulo p_256, z := (-x) mod p_256, assuming x reduced */
/*  Input x[4]; output z[4] */
extern void bignum_neg_p256 (uint64_t z[4], uint64_t x[4]);

/*  Negate modulo p_256k1, z := (-x) mod p_256k1, assuming x reduced */
/*  Input x[4]; output z[4] */
extern void bignum_neg_p256k1 (uint64_t z[4], uint64_t x[4]);

/*  Negate modulo p_384, z := (-x) mod p_384, assuming x reduced */
/*  Input x[6]; output z[6] */
extern void bignum_neg_p384 (uint64_t z[6], uint64_t x[6]);

/*  Negate modulo p_521, z := (-x) mod p_521, assuming x reduced */
/*  Input x[9]; output z[9] */
extern void bignum_neg_p521 (uint64_t z[9], uint64_t x[9]);

/*  Negated modular inverse, z := (-1/x) mod 2^{64k} */
/*  Input x[k]; output z[k] */
extern void bignum_negmodinv (uint64_t k, uint64_t *z, uint64_t *x);

/*  Test bignum for nonzero-ness x =/= 0 */
/*  Input x[k]; output function return */
extern uint64_t bignum_nonzero (uint64_t k, uint64_t *x);

/*  Test 256-bit bignum for nonzero-ness x =/= 0 */
/*  Input x[4]; output function return */
extern uint64_t bignum_nonzero_4(uint64_t x[4]);

/*  Test 384-bit bignum for nonzero-ness x =/= 0 */
/*  Input x[6]; output function return */
extern uint64_t bignum_nonzero_6(uint64_t x[6]);

/*  Normalize bignum in-place by shifting left till top bit is 1 */
/*  Input z[k]; outputs function return (bits shifted left) and z[k] */
extern uint64_t bignum_normalize (uint64_t k, uint64_t *z);

/*  Test bignum for odd-ness */
/*  Input x[k]; output function return */
extern uint64_t bignum_odd (uint64_t k, uint64_t *x);

/*  Convert single digit to bignum, z := n */
/*  Input n; output z[k] */
extern void bignum_of_word (uint64_t k, uint64_t *z, uint64_t n);

/*  Optionally add, z := x + y (if p nonzero) or z := x (if p zero) */
/*  Inputs x[k], p, y[k]; outputs function return (carry-out) and z[k] */
extern uint64_t bignum_optadd (uint64_t k, uint64_t *z, uint64_t *x, uint64_t p, uint64_t *y);

/*  Optionally negate, z := -x (if p nonzero) or z := x (if p zero) */
/*  Inputs p, x[k]; outputs function return (nonzero input) and z[k] */
extern uint64_t bignum_optneg (uint64_t k, uint64_t *z, uint64_t p, uint64_t *x);

/*  Optionally negate modulo p_256, z := (-x) mod p_256 (if p nonzero) or z := x (if p zero), assuming x reduced */
/*  Inputs p, x[4]; output z[4] */
extern void bignum_optneg_p256 (uint64_t z[4], uint64_t p, uint64_t x[4]);

/*  Optionally negate modulo p_256k1, z := (-x) mod p_256k1 (if p nonzero) or z := x (if p zero), assuming x reduced */
/*  Inputs p, x[4]; output z[4] */
extern void bignum_optneg_p256k1 (uint64_t z[4], uint64_t p, uint64_t x[4]);

/*  Optionally negate modulo p_384, z := (-x) mod p_384 (if p nonzero) or z := x (if p zero), assuming x reduced */
/*  Inputs p, x[6]; output z[6] */
extern void bignum_optneg_p384 (uint64_t z[6], uint64_t p, uint64_t x[6]);

/*  Optionally negate modulo p_521, z := (-x) mod p_521 (if p nonzero) or z := x (if p zero), assuming x reduced */
/*  Inputs p, x[9]; output z[9] */
extern void bignum_optneg_p521 (uint64_t z[9], uint64_t p, uint64_t x[9]);

/*  Optionally subtract, z := x - y (if p nonzero) or z := x (if p zero) */
/*  Inputs x[k], p, y[k]; outputs function return (carry-out) and z[k] */
extern uint64_t bignum_optsub (uint64_t k, uint64_t *z, uint64_t *x, uint64_t p, uint64_t *y);

/*  Optionally subtract or add, z := x + sgn(p) * y interpreting p as signed */
/*  Inputs x[k], p, y[k]; outputs function return (carry-out) and z[k] */
extern uint64_t bignum_optsubadd (uint64_t k, uint64_t *z, uint64_t *x, uint64_t p, uint64_t *y);

/*  Return bignum of power of 2, z := 2^n */
/*  Input n; output z[k] */
extern void bignum_pow2 (uint64_t k, uint64_t *z, uint64_t n);

/*  Shift bignum left by c < 64 bits z := x * 2^c */
/*  Inputs x[n], c; outputs function return (carry-out) and z[k] */
extern uint64_t bignum_shl_small (uint64_t k, uint64_t *z, uint64_t n, uint64_t *x, uint64_t c);

/*  Shift bignum right by c < 64 bits z := floor(x / 2^c) */
/*  Inputs x[n], c; outputs function return (bits shifted out) and z[k] */
extern uint64_t bignum_shr_small (uint64_t k, uint64_t *z, uint64_t n, uint64_t *x, uint64_t c);

/*  Square, z := x^2 */
/*  Input x[n]; output z[k] */
extern void bignum_sqr (uint64_t k, uint64_t *z, uint64_t n, uint64_t *x);

/*  Square, z := x^2 */
/*  Input x[4]; output z[8] */
extern void bignum_sqr_4_8 (uint64_t z[8], uint64_t x[4]);

/*  Square, z := x^2 */
/*  Input x[6]; output z[12] */
extern void bignum_sqr_6_12 (uint64_t z[12], uint64_t x[6]);

/*  Square, z := x^2 */
/*  Input x[8]; output z[16] */
extern void bignum_sqr_8_16 (uint64_t z[16], uint64_t x[8]);

/*  Square modulo p_256k1, z := (x^2) mod p_256k1 */
/*  Input x[4]; output z[4] */
extern void bignum_sqr_p256k1 (uint64_t z[4], uint64_t x[4]);

/*  Square modulo p_521, z := (x^2) mod p_521, assuming x reduced */
/*  Input x[9]; output z[9] */
extern void bignum_sqr_p521 (uint64_t z[9], uint64_t x[9]);

/*  Subtract, z := x - y */
/*  Inputs x[m], y[n]; outputs function return (carry-out) and z[p] */
extern uint64_t bignum_sub (uint64_t p, uint64_t *z, uint64_t m, uint64_t *x, uint64_t n, uint64_t *y);

/*  Subtract modulo p_256, z := (x - y) mod p_256, assuming x and y reduced */
/*  Inputs x[4], y[4]; output z[4] */
extern void bignum_sub_p256 (uint64_t z[4], uint64_t x[4], uint64_t y[4]);

/*  Subtract modulo p_256k1, z := (x - y) mod p_256k1, assuming x and y reduced */
/*  Inputs x[4], y[4]; output z[4] */
extern void bignum_sub_p256k1 (uint64_t z[4], uint64_t x[4], uint64_t y[4]);

/*  Subtract modulo p_384, z := (x - y) mod p_384, assuming x and y reduced */
/*  Inputs x[6], y[6]; output z[6] */
extern void bignum_sub_p384 (uint64_t z[6], uint64_t x[6], uint64_t y[6]);

/*  Subtract modulo p_521, z := (x - y) mod p_521, assuming x and y reduced */
/*  Inputs x[9], y[9]; output z[9] */
extern void bignum_sub_p521 (uint64_t z[9], uint64_t x[9], uint64_t y[9]);

/*  Convert 4-digit (256-bit) bignum to big-endian bytes */
/*  Input x[4]; output z[32] (bytes) */
extern void bignum_tobebytes_4 (uint8_t z[32], uint64_t x[4]);

/*  Convert 6-digit (384-bit) bignum to big-endian bytes */
/*  Input x[6]; output z[48] (bytes) */
extern void bignum_tobebytes_6 (uint8_t z[48], uint64_t x[6]);

/*  Convert 4-digit (256-bit) bignum to little-endian bytes */
/*  Input x[4]; output z[32] (bytes) */
extern void bignum_tolebytes_4 (uint8_t z[32], uint64_t x[4]);

/*  Convert 6-digit (384-bit) bignum to little-endian bytes */
/*  Input x[6]; output z[48] (bytes) */
extern void bignum_tolebytes_6 (uint8_t z[48], uint64_t x[6]);

/*  Convert to Montgomery form z := (2^256 * x) mod p_256 */
/*  Input x[4]; output z[4] */
extern void bignum_tomont_p256 (uint64_t z[4], uint64_t x[4]);

/*  Convert to Montgomery form z := (2^256 * x) mod p_256k1 */
/*  Input x[4]; output z[4] */
extern void bignum_tomont_p256k1 (uint64_t z[4], uint64_t x[4]);

/*  Convert to Montgomery form z := (2^384 * x) mod p_384 */
/*  Input x[6]; output z[6] */
extern void bignum_tomont_p384 (uint64_t z[6], uint64_t x[6]);

/*  Convert to Montgomery form z := (2^576 * x) mod p_521 */
/*  Input x[9]; output z[9] */
extern void bignum_tomont_p521 (uint64_t z[9], uint64_t x[9]);

/*  Triple modulo p_256, z := (3 * x) mod p_256 */
/*  Input x[4]; output z[4] */
extern void bignum_triple_p256 (uint64_t z[4], uint64_t x[4]);

/*  Triple modulo p_256k1, z := (3 * x) mod p_256k1 */
/*  Input x[4]; output z[4] */
extern void bignum_triple_p256k1 (uint64_t z[4], uint64_t x[4]);

/*  Triple modulo p_384, z := (3 * x) mod p_384 */
/*  Input x[6]; output z[6] */
extern void bignum_triple_p384 (uint64_t z[6], uint64_t x[6]);

/*  Triple modulo p_521, z := (3 * x) mod p_521, assuming x reduced */
/*  Input x[9]; output z[9] */
extern void bignum_triple_p521 (uint64_t z[9], uint64_t x[9]);

/*  Reverse the bytes in a single word */
/*  Input a; output function return */
extern uint64_t word_bytereverse (uint64_t a);

/*  Count leading zero bits in a single word */
/*  Input a; output function return */
extern uint64_t word_clz (uint64_t a);

/*  Count trailing zero bits in a single word */
/*  Input a; output function return */
extern uint64_t word_ctz (uint64_t a);

/*  Return maximum of two unsigned 64-bit words */
/*  Inputs a, b; output function return */
extern uint64_t word_max (uint64_t a, uint64_t b);

/*  Return minimum of two unsigned 64-bit words */
/*  Inputs a, b; output function return */
extern uint64_t word_min (uint64_t a, uint64_t b);

/*  Single-word negated modular inverse (-1/a) mod 2^64 */
/*  Input a; output function return */
extern uint64_t word_negmodinv (uint64_t a);

/*  Single-word reciprocal, 2^64 + ret = ceil(2^128/a) - 1 if MSB of "a" is set */
/*  Input a; output function return */
extern uint64_t word_recip (uint64_t a);
