---
rg: 2
id: rational-eigenvalue-iff-subshift-ring-is-matrix-ring
kind: claim
title: A minimal Cantor system has eigenvalue e^(2πi/p) iff its crossed product over F_q is a p×p matrix ring, and then EL_n of it is EL_(np) over the induced system
distinct_from:
  subshift-crossed-product-k0-is-coinvariant-group: that computes the K_0 group of the crossed product; this uses it to identify p-divisibility of the unit with rational spectrum and with matrix-ring decompositions of the ring and of its elementary groups
artifacts:
  - research/artifacts/sk-open-4-dictionary-2026-09-13-part2.md
---

Let `(X,T)` be an infinite minimal Cantor system, `q` a prime power, `R_X = LC(X,F_q) ⋊_T Z` and `p ≥ 2`. The
following are equivalent:
1. `e^(2πi/p)` is a continuous eigenvalue of `(X,T)`;
2. there is a clopen `U` with `X = U ⊔ TU ⊔ … ⊔ T^(p−1)U`;
3. `[χ_X] ∈ p·K^0(X,T)`, where `K^0(X,T) = C(X,Z)/(1−T_*)C(X,Z)`;
4. `M_p(F_q)` embeds unitally in `R_X`;
5. `R_X ≅ M_p(S)` for some unital ring `S`.

Under (2):
- `R_X ≅ M_p(LC(U,F_q) ⋊_(T^p) Z)`, and `(U,T^p)` is an infinite minimal Cantor system. If `X` is a subshift, so is `(U,T^p)`, over p-blocks.
- For every `n ≥ 2`, `EL_n(R_X) ≅ EL_(np)(LC(U,F_q) ⋊_(T^p) Z)` and `SL_(np)(F_q[t,t^(−1)]) ≤ EL_n(R_X)`.
- Any factor map `X → Y` of Cantor systems gives a unital embedding `R_Y ⊆ R_X`, so `EL_n(R_Y) ≤ EL_n(R_X)`.

For the note's group `G_X = EL_3(LC(X,F_2) ⋊ Z)`: when `X` has a rational eigenvalue `e^(2πi/p)`, `G_X` is also an
elementary group of rank `3p` over an induced subshift ring, and it contains the S-arithmetic lattice
`SL_(3p)(F_2[t,t^(−1)])`. The rank 3 is not an invariant of the family.

Proof in the `-proof` route; details in the artifact, §1. Unreviewed.
