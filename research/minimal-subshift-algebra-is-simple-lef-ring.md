---
rg: 2
id: minimal-subshift-algebra-is-simple-lef-ring
kind: claim
title: The algebraic crossed product of an infinite minimal subshift over a finite field is a finitely generated simple LEF ring
artifacts:
  - research/artifacts/simple-kazhdan-lef-subshift-elementary-group-2026-09-12.md
---

Let `q` be a prime power, `X` an infinite minimal subshift over a finite alphabet `A`, `T` the
shift, and `R = LC(X,F_q) ⋊_T Z` the algebraic crossed product: finite sums `sum_j f_j u^j` with
`f_j` locally constant and `u f u^(-1) = f o T^(-1)`. Then:

1. `R` is generated as a ring by `u`, `u^(-1)` and the letter cylinders `chi_[x_0=a]`.
2. `R` is simple, with centre `F_q`.
3. `R` is LEF as a ring. There is an injective unital ring homomorphism
   `R -> prod_omega M_(N_k)(F_q)` into an algebraic ultraproduct of full matrix algebras. It comes
   from periodic words `w_k` whose cyclic windows of length `2k+1` are exactly the words of
   `L_(2k+1)(X)`.

Consequently `GL_n(R)`, and every finitely generated subgroup of it, embeds in an ultraproduct of
the finite groups `GL_(nN_k)(F_q)` and is LEF.
