---
rg: 2
id: elementary-groups-fixed-price-one-root-cycle-proof
kind: route
title: Grow E_n(A) from one root subgroup, adding root elements that commute with an already present root subgroup
target: elementary-groups-over-infinite-rings-have-fixed-price-one
requires: [gaboriau-commensurated-chain-fixed-price-criterion]
---

**Commutator rule.** Over any ring, `[x_ij(a), x_kl(b)] = 1` whenever `j != k` and `i != l`.
So `x_ij(a)` commutes with the whole root subgroup `U_kl`.

**Order of the roots.**
1. The six roots of the `3 x 3` corner, in the order `12, 13, 23, 21, 31, 32`. Each commutes
   with the previous one: `(13)` with `U_12`, `(23)` with `U_13`, `(21)` with `U_23`, `(31)`
   with `U_21`, `(32)` with `U_31`.
2. Every other root `(i, j)`, in any order.
   - If `j != 1` and `i != 2`, it commutes with `U_12`.
   - If `j = 1`, then `i >= 4` and it commutes with `U_23`.
   - If `i = 2`, then `j >= 4` and it commutes with `U_13`.

**The chain.**
- Put `Γ_1 = U_12 ≅ (A, +)`, infinite and abelian, hence of fixed price one.
- Add the elements `x_ij(b)`, root by root in the order above and one element at a time. When
  `γ = x_ij(b)` is added, some root subgroup `U` commuting with it is already in the current
  stage, so `γ^(-1) Γ_m γ ∩ Γ_m ⊇ U` is infinite.
- Every stage contains `U_12`, so it is infinite. The union contains every root subgroup, so it
  is `E_n(A)`.
- Criterion VI.24(3) gives fixed price one.
