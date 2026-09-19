---
rg: 2
id: fpbs-free-group-sandwich-cost-is-two-proof
kind: route
title: Pass to a rank-two subgroup, which is compressed in F_2, and apply the Fox-rank sandwich bound
target: fpbs-free-group-sandwich-cost-is-two
requires:
  - fpbs-sandwich-cost-fox-rank-lower-bound
  - gaboriau-treeable-free-action-realizes-min-cost
---

Let `a` be a free p.m.p. action of `F_2`, let `K ≤ F_2` be finitely
generated and non-cyclic, and let `E_{a|K} ⊆ E ⊆ E_a`.

1. **A rank-two subgroup.** `K` contains non-commuting `u` and `v`. Then
   `K' = ⟨u, v⟩` is free of rank exactly 2 with basis `u, v`.
2. **It is compressed.** Every finitely generated `L ⊇ K'` is non-abelian and
   free, so `rk L ≥ 2`.
3. **Lower bound.** `E ⊇ E_{a|K'}`. Part (2) of
   `fpbs-sandwich-cost-fox-rank-lower-bound` gives `C(E) ≥ 2`.
4. **Upper bound.** The basis `{f_1, f_2}` gives a treeing of `E_a`. By
   `gaboriau-treeable-free-action-realizes-min-cost` (1), `C(E_a) = 2`.

So `p^{F_2}_K(a) = 2`. This is part (3) of the target claim of the bound,
proved in §4 of `fpbs-sandwich-cost-fox-rank-lower-bound-proof`.

**Structural note.** The finite-coset/infinite-coset split and MC_∞ are not
needed. The malnormal core `K = ⟨a, bab^{-2}⟩` is covered, because every
rank-2 subgroup of `F_2` is compressed. The twisted non-group sandwiches that
the earlier attempts left open are covered too: the bound applies to every
graphing inside `E_a`.
