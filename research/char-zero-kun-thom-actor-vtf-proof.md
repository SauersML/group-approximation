---
rg: 2
id: char-zero-kun-thom-actor-vtf-proof
kind: route
title: Roots of unity make the characteristic polynomial constant, and Minkowski finishes at x = 1
target: char-zero-kun-thom-actor-has-torsion-free-finite-index-subgroup
requires: []
---

**`H` is a subgroup of finite index.**
- Substitution maps elementary matrices to elementary matrices, so it
  preserves `EL_r(R)`.
- Substitution fixes the point `x = 1`, so evaluation at 1 commutes with
  every `alpha_A`. Hence `K` is `SL_d(Z)`-invariant and `H` is a subgroup.
- `K` has finite image in `GL_r(F_p)`, and `Gamma_d(p)` has finite index, so
  `H` has finite index in `G_0`.

**`H` is torsion-free.**
1. Let `(M, A)` in `H` have finite order. Its image `A` lies in `Gamma_d(p)`
   and has finite order, so `A = I` by Minkowski's lemma: the kernel of
   reduction mod `p >= 3` in `GL_d(Z)` is torsion-free. Then
   `(M, I)^n = (M^n, I)`, so `M` has finite order.
2. Over the algebraic closure of `Q(x_1,...,x_d)`, a finite-order `M` is
   diagonalizable with root-of-unity eigenvalues. The coefficients of its
   characteristic polynomial are symmetric functions of roots of unity, so
   they are algebraic over `Q`. They also lie in `R`. A nonconstant Laurent
   polynomial is transcendental over `Q`, so the coefficients are integers.
3. Evaluating at `x = 1` commutes with taking characteristic polynomials and
   fixes integer constants. So `chi_M = chi_(M(1))`.
4. `M(1)` lies in `GL_r(Z)`, satisfies `M(1) = I mod p`, and has finite
   order, so `M(1) = I` by Minkowski. Hence `chi_M = (T-1)^r`.
5. A diagonalizable matrix whose eigenvalues are all 1 is `I`. So `M = I`.

QED
