---
rg: 2
id: laurent-linear-confining-sets-force-infinite-order-elements
kind: claim
title: "A subgroup confined by a finite subset of SL_3(F_2[u^{±1}]) ∖ {1}, in any group containing SL_3(F_2[u^{±1}]), contains an element of infinite order"
artifacts:
  - research/artifacts/sk-cstar-genericity-2026-09-14-part1.md
distinct_from:
  elementary-root-subgroups-over-crossed-products-are-not-confined: that shows specific amenable test subgroups are not confined; this constrains every confined subgroup whose confining set is Laurent-linear, whatever the subgroup is
---

**ESTABLISHED (unreviewed).** Let `Λ = SL_3(F_2[u^{±1}])` and let `Γ ⊇ Λ` be a group (for example `G_X = EL_3(LC(X,F_2)⋊Z)` for any infinite minimal subshift `X`, since `Λ = EL_3(F_2[u^{±1}])`). If `H ≤ Γ` is confined by a finite `P ⊆ Λ∖{1}`, then `H` contains a `Γ`-conjugate of an element of `Λ` of infinite order.

**Corollary.** No nontrivial torsion subgroup of `G_X` is confined by a subset of `EL_3(F_2)∖{1}`. This covers the constant units excluded from configurations by `idempotent-displacement-fails-for-polynomially-small-units`: involutions, `I+E_12+E_23`, the Singer cycles.

**Scope.** This is (L3) of the idempotent route for Laurent-linear confining sets only. General confining sets in `G_X` stay open: the trace argument needs commutative coefficients (artifact §4).
