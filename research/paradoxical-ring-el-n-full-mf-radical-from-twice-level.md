---
rg: 2
id: paradoxical-ring-el-n-full-mf-radical-from-twice-level
kind: claim
title: If (n+1)[R] <= n[R] in V(R), every homomorphism from EL_N(R) to an MF group is trivial for all N >= 2n
distinct_from:
  full-defect-ring-non-mf-at-rank-two: that needs a one-sided inverse with full complement in R itself; this needs only stable paradoxicality of [R] and applies the rank-two theorem to M_n(R), at the cost of the rank 2n.
  simple-dedekind-infinite-ring-elementary-full-mf-radical: that is the simple not directly finite case, which is paradoxical level 1; this covers rings that are directly finite but not stably finite, at every level.
artifacts:
  - research/artifacts/un-middle-stable-paradox-threshold-2026-09-13.md
---

Let `R` be a countable unital ring and `n ≥ 1`, and suppose `(n+1)[R] ≤ n[R]` in the Murray–von Neumann monoid `V(R)`
with the algebraic preorder. Equivalently, `R^n ≅ R^{n+1} ⊕ Q` for some f.g. projective `Q`.

Then for every `N ≥ 2n`, every homomorphism from `EL_N(R)` to an MF group is trivial: `Rad_MF(EL_N(R)) = EL_N(R)`.

- Finite generation, simplicity and property (T) are not assumed.
- Calibrations: `L_k(1,m)` has level 1, giving `N ≥ 2`. Leavitt algebras of module type `L_k(m,n)`, `2 ≤ m < n`, have
  level at most `m`, giving `N ≥ 2m`.
- A ring embedding unitally in a matrix ultraproduct has a state at `[R]`, so it has no paradoxical level, and the
  theorem is silent.
