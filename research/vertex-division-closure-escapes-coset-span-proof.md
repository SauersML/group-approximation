---
rg: 2
id: vertex-division-closure-escapes-coset-span-proof
kind: route
title: Invert 1+s in the affiliated algebra, then rule it out of the skew Laurent ring of units
target: vertex-division-closure-escapes-edge-coset-span
requires:
  - subgroup-cosets-are-independent-over-division-closure
artifacts:
  - research/artifacts/atiyah-coproduct-inner-rank-2026-09-12.md
---

Write `P = <C, s> <= A`, so `P` is the ascending union of `C`-cosets `C s^k`,
`k in Z`, all distinct because `s` has infinite order in `N_A(C)/C`.

1. **`(1 + s)^(-1)` exists in `D_A`.** Under `l^2(P) = l^2(C) (x) l^2(Z)` and
   Fourier transform on the second factor, `1 + lambda(s)` becomes
   multiplication by `1 + z` on `l^2(C) (x) L^2(T)`. The zero set `{z = -1}` is
   Lebesgue null, so `1 + lambda(s)` is injective with dense range, hence
   invertible in `U(P) <= U(A)`. Since `1 + s in K[A]`, its inverse lies in the
   division closure `D_A`.

2. **The span is a skew Laurent ring.** By
   [[subgroup-cosets-are-independent-over-division-closure]],
   `span_(D_C)(P) = (+)_k D_C s^k` is free as a left `D_C`-module on the powers
   of `s`. Conjugation by `s` carries `C` to `C`, hence carries `K[C]` to
   `K[C]`, and being implemented by a unitary of `l^2` it carries `U(C)` to
   `U(C)` and the division closure `D_C` to `D_C`. Write `sigma` for the induced
   automorphism. Then multiplication makes the span the skew Laurent ring

   ```text
   span_(D_C)(P) = D_C[s^(+-1); sigma].
   ```

3. **Its units are monomials.** `D_C` is a ring with no zero divisors in the
   relevant degrees: for `d, e in D_C` nonzero, `(d s^j)(e s^k) = d sigma^j(e) s^(j+k)`
   is nonzero. So the top and bottom degrees of a product add, and a product of
   two nonzero elements is `1` only if both are monomials `d s^k`.

4. **`1 + s` is not a monomial.** It has nonzero coefficients in degrees `0` and
   `1`, so by step 3 it is not invertible in `D_C[s^(+-1); sigma]`.

5. **Conclusion.** If `(1 + s)^(-1)` were in `span_(D_C)(A)`, then, multiplying
   the relation `(1+s)(1+s)^(-1) = 1` out and comparing coset components by the
   freeness of step 2, `(1+s)^(-1)` would lie in `span_(D_C)(P)` and invert
   `1 + s` there, contradicting step 4. QED

The same argument runs verbatim with `1 + s` replaced by any element of
`K[P]` supported on at least two `C`-cosets and invertible in `U(P)`.
