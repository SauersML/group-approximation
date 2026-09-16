---
rg: 2
id: virtually-free-by-cyclic-normal-fibre-gives-gd-two
kind: claim
title: Torsion-free virtually free-by-cyclic groups with a normal fibre or periodic monodromy have gd two
distinct_from:
  torsion-free-virtually-free-by-cyclic-groups-have-gd-two: that is the open statement for every torsion-free virtually free-by-cyclic group; this proves it when some fibre is normal in the whole group or the monodromy is periodic.
  free-by-virtually-cyclic-torsion-free-groups-have-gd-two: that is the general tree-quotient lemma; this applies it to finite extensions of free-by-cyclic groups, including the virtually F_n x Z case, where the normal free subgroup is a center rather than a fibre.
artifacts:
  - research/artifacts/eg-special-case-virtually-free-by-cyclic-2026-09-16.md
---

Let `G` be a torsion-free group. Then `gd G = cd G ≤ 2`, so the Eilenberg--Ganea conjecture
holds for `G`, in either of the following cases.

- **(i) Normal fibre.** Some finite-index subgroup `H ≤ G` has a surjection `χ: H → Z` whose
  kernel is free (of any rank) and normal in `G`. In particular this holds if:
  - `H = F ⋊ Z` is normal in `G` and every `G`-conjugate of the projection `ψ: H → Z` is `±ψ`.
    This is automatic when `b_1(H) = 1`.
  - `H ⊲ G` and some `G`-invariant surjection `H → Z` has free kernel. In that case `G` is itself
    free-by-cyclic.
- **(ii) Periodic monodromy.** `G` has a finite-index subgroup `F_n × Z` with `2 ≤ n < ∞`. In
  particular this holds if `G` contains `F_n ⋊_φ Z` with finite index and `φ` of finite order
  in `Out(F_n)`.
  - Here the normal free subgroup used is the center `Z(H)` of the normal core `H`, and
    `G/Z(H)` is virtually free.

What remains open is the case where the `Q`-orbit of every fibration spans rank at least 2
and the monodromy is not periodic. That is
`torsion-free-virtually-free-by-cyclic-groups-have-gd-two`.
