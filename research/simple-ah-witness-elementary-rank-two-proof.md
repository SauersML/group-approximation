---
rg: 2
id: simple-ah-witness-elementary-rank-two-proof
kind: route
title: Subdivide a null-homotopy over the sphere and flatten the blocks
target: simple-ah-witness-is-elementary-in-rank-two
requires:
  - stw59-simple-ah-non-k1-injective
artifacts:
  - research/artifacts/ah-k1-mf-bridge-2026-09-07.md
---

## Proof

Represent the generator of `pi_4(U(2)) = Z/2` by `u : S^4 -> SU(2)`, which
is possible because `pi_4(SU(2)) = pi_4(S^3) = Z/2` maps onto it.

`pi_4(U(n))` is stable for `n >= 3` and `pi_4(U) = 0`, so `diag(u, I_2)` is
null-homotopic as a map `S^4 -> SU(4)`.

A null-homotopic map `S^4 -> SL_4(C)` is elementary over `C(S^4)`: subdivide
the null-homotopy so that consecutive matrices differ by less than the
invertibility margin, so that each increment is within the norm ball where
Gaussian elimination writes an invertible matrix as a product of elementary
matrices and one diagonal matrix, and factor each determinant-one diagonal by
the Whitehead identity.  So

```text
diag(u, I_2) in E_4(C(S^4)).
```

Block flattening gives `E_4(C(S^4)) = E_2(M_2(C(S^4)))`: the cross-block
elementary roots generate the block-elementary subgroup, and each within-block
root is a commutator of two cross-block roots through an index in the other
block.

Applying the initial-stage unital homomorphism of the AH system to
coefficients carries this factorization to `A` and sends `u` to `v`, so
`diag(v,1_A) in E_2(A)`.  A class with `diag(v,1) in E_2(A)` is zero in
`GL_infinity(A)/E_infinity(A)`.
