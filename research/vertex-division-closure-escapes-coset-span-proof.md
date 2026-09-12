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

1. **`(1 + s)^(-1)` exists in `D_A`.** `s` has infinite order, and `l^2(A)` is
   the orthogonal sum of the `l^2(<s> g)` over the right cosets of `<s>`. On
   each of these `lambda(s)` is the bilateral shift. After Fourier transform,
   `1 + lambda(s)` is multiplication by `1 + z` on `L^2(T) (x) l^2(<s>\A)`. The
   zero set `{z = -1}` is Lebesgue null, so `1 + lambda(s)` is injective with
   dense range, so it is invertible in `U(A)`. Since `1 + s in K[A]`, its
   inverse lies in the division closure `D_A`.
   *Corrected 2026-09-12 (swarm4-reviewer).* The earlier text used
   `l^2(P) = l^2(C) (x) l^2(Z)`, under which `lambda(s)` is `U_sigma (x) shift`,
   not `1 (x) shift`, unless `s` centralizes `C`.

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

3. **Extreme degrees.** Let `y = sum_(k=m..M) y_k s^k` in
   `D_C[s^(+-1); sigma]` with `y_m != 0 != y_M`. In `(1 + s) y` the coefficient
   of `s^m` is `y_m`, and the coefficient of `s^(M+1)` is `sigma(y_M)`. Both are
   nonzero, because the extreme coefficients of `1 + s` are `1` and `sigma` is
   an automorphism.

4. **`1 + s` has no right inverse there.** If `(1 + s) y = 1`, step 3 forces
   `m = 0` and `M + 1 = 0`, which contradicts `m <= M`.
   *Corrected 2026-09-12 (swarm4-reviewer).* The earlier step 3 asserted that
   `D_C` has no zero divisors. That needs torsion-freeness and Strong Atiyah
   for `C`, which the claim does not assume, and the argument does not use it.

5. **Conclusion.** If `(1 + s)^(-1)` were in `span_(D_C)(A)`, then, multiplying
   the relation `(1+s)(1+s)^(-1) = 1` out and comparing coset components by the
   freeness of step 2, `(1+s)^(-1)` would lie in `span_(D_C)(P)` and invert
   `1 + s` there, contradicting step 4. QED

The same argument works for any element of `K[P]` that is supported on at
least two `C`-cosets, is invertible in `U(P)`, and has extreme coefficients
that are non-zero-divisors of `D_C`. When `D_C` is a division ring, every such
element qualifies. Without the coefficient condition the statement is false.
Take `P = Z/2 x Z`, `C = Z/2 = <eps>` and `e = (1 + eps)/2`. The element
`e + (1 - e)s` is supported on two `C`-cosets, and its inverse
`e + (1 - e)s^(-1)` lies in `K[P]`.
