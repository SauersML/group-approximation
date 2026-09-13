---
rg: 2
id: soft-kazhdan-central-elements-fixed-by-normal-closure-proof
kind: route
title: Read the soft element as a Lambda-fixed diagonal, tensor the permutation part into a sofic representation, and apply the normal-closure theorem
target: soft-kazhdan-central-elements-fixed-by-normal-closure
requires:
  - normal-closure-fixes-gamma-fixed-algebra
artifacts:
  - research/artifacts/ex-q34-kt-wreath-soft-kernel-part2-2026-09-13.md
  - research/artifacts/ex-q34-kt-wreath-soft-kernel-2026-09-13.md
---

Full proof: Theorem M of
`research/artifacts/ex-q34-kt-wreath-soft-kernel-part2-2026-09-13.md`.  The
monomial facts (HC) and (COV) are in part 1, §1.

1. **Permutation part.**  For monomials, `d_H(pi M, pi M') <= ||M - M'||_2^2 / 2`,
   so `psi = pi_omega o rho` is a homomorphism.  Since
   `||(c; sigma) - (c; id)||_2^2 = 2 d_H(sigma, id)`, `psi(a) = 1` makes
   `b = rho(a)` a diagonal unitary in `D_omega`.
2. **Covariance.**  `(c; sigma) f (c; sigma)^* = f o sigma^(-1)` for diagonal
   `f`, because the phases cancel.  For `l in Lambda`,
   `psi(l) . b = rho(l a l^(-1)) = b`.
3. **Tensoring.**  Let `lambda : G -> prod_omega Sym(Z_m)` be a sofic
   representation (trace `0` off the identity), which exists because `G` is
   sofic.  Then `sigma' = psi|G × lambda` is a homomorphism whose traces are
   products, hence `0` off the identity.  And `sigma'(l) . (b ⊗ 1) = b ⊗ 1`.
4. **Normal closure.**  Part 2 of `normal-closure-fixes-gamma-fixed-algebra`
   (for `Lambda` infranormal in `G`, both Kazhdan) says every
   `n in <<Lambda>>_G` fixes `D^(sigma'(Lambda))` pointwise.  So
   `psi(n) . b = b`.
5. **Conclusion.**  By covariance again,
   `rho(n a n^(-1)) = rho(n) b rho(n)^* = psi(n) . b = b`.
