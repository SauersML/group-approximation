---
rg: 2
id: automatic-groups-of-finite-vcd-p-subgroup-classes-proof
kind: route
title: Finite vcd plus FP_infinity makes total mod-p cohomology finite, and Brown's lemma then counts the p-subgroups
target: automatic-finite-vcd-groups-have-few-p-subgroup-classes
requires:
  - brown-finite-p-subgroup-classes-from-finite-mod-p-cohomology
  - finite-index-subgroups-of-automatic-groups-are-automatic
  - automatic-groups-are-of-type-f-infinity
---

Let `G` be automatic, `S` a finite generating set, and `H_0 ≤ G` torsion-free of finite index
with `cd_Z H_0 = k < ∞`. Fix a prime `p`.

**Step 1 (normal core).** Let `H = ⋂_{g ∈ G} g H_0 g^{-1}`. Only finitely many conjugates
occur, one per coset of `H_0`, so `H` is a finite intersection of finite-index subgroups. It is
therefore normal of finite index. As a subgroup of `H_0` it is torsion-free, and
`cd_Z H ≤ cd_Z H_0 = k`, since cd does not increase on passing to subgroups (restrict a
projective resolution).

**Step 2 (degreewise finiteness).** `H` has finite index in `G`, so it is automatic by
`finite-index-subgroups-of-automatic-groups-are-automatic`. By
`automatic-groups-are-of-type-f-infinity` it is then of type `FP_∞`. Choose a free resolution
`F_* → Z` over `ZH` with each `F_n` finitely generated, of rank `r_n`. Then
`Hom_{ZH}(F_n, F_p) ≅ F_p^{r_n}` is finite. So `H^n(H;F_p)`, a subquotient of it, is finite for
every `n`.

**Step 3 (vanishing above k).** Since `cd_Z H ≤ k`, there is a projective resolution of `Z` over
`ZH` of length `k`. So `H^n(H;M) = 0` for all `n > k` and every `ZH`-module `M`, including
`M = F_p`. With Step 2, `⊕_n H^n(H;F_p) = ⊕_{n ≤ k} H^n(H;F_p)` is finite.

**Step 4 (Brown).** `H` is a finite-index torsion-free normal subgroup of `G` with finite total
mod-p cohomology. By `brown-finite-p-subgroup-classes-from-finite-mod-p-cohomology`, `G` has
finitely many conjugacy classes of finite `p`-subgroups. Choose representatives `P_1, …, P_m`.
This is item 1.

**Step 5 (orders and ball).** Every finite subgroup `F ≤ G` meets `H` trivially, so it embeds in
`G/H`, and `|F| ≤ [G:H]`. This gives item 2 for all finite subgroups at once. Each `P_i` is
finite. Put `R_p = max { |x|_S : x ∈ P_1 ∪ … ∪ P_m }`. Any finite `p`-subgroup is
`g P_i g^{-1} ⊆ g B_S(R_p) g^{-1}` for some `g` and `i`, which is item 3. A prime `p` not
dividing `[G:H]` has no nontrivial finite `p`-subgroups. Taking the maximum of `R_p` over the
finitely many primes dividing `[G:H]` gives a single `R` that works for all primes.

**Contrapositive.** If the conclusion fails, the hypothesis fails: either no torsion-free subgroup
of finite index exists, or each one has infinite cd. Each one is automatic by Step 2's first
citation. This is the stated localisation.
