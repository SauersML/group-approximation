---
rg: 2
id: ascending-hnn-coset-ray-is-folner-proof
kind: route
title: Height truncation makes every element act as a translation on the tail
target: ascending-hnn-coset-ray-is-folner
requires: []
artifacts:
  - GroupApproximation/Sofic/AscendingHNNFolner.lean
---

## Why sufficient

Machine-checked, no `sorry`, no axiom, no literature premise: the Monod--Popa
theorem is *not* imported, the Følner sets are built.  Sections 10.1--10.3 of
the dossier, in four steps.

**The ray is injective.**  `ray_injective`: the height homomorphism
`right : V -> Z` kills the base copy of `Gamma` (`right_iotaVertical`) and sends
`t^j` to `j` (`right_tVertical_zpow`), so `x_{j_1} = x_{j_2}` forces
`j_1 - j_2 = 0`.

**Levels stabilize tails of the ray.**  `inl_level_eq_conj` identifies the
level-`n` subgroup with `t^n Gamma t^{-n}` inside the model, and
`tVertical_pow_conj_mem` puts `t^n x t^{-n}` in the base for `x` in `Gamma`.
Hence a conjugate deep enough fixes `x_j` for all `j` beyond a bound depending
only on the element.

**Every element eventually translates.**  `smul_ray_eq` is the key lemma: for
each `g` in `V` there is `M(g)` with `g . x_j = x_{j - h(g)}` for all
`j >= M(g)`, where `h(g)` is the height of `g`.  Beyond `M(g)` the base part of
`g` has been absorbed into a level that stabilizes the point, so only the height
translation survives.  `tVertical_zpow_smul_ray` is the pure-translation case.

**Intervals are Følner.**  `card_symmDiff_Ico_le`: two integer intervals of the
same length `L` have `|Ico a (a+L) ∆ Ico b (b+L)| <= 2|a - b|`, proved by
containing the symmetric difference in two intervals of length `|a-b|`.
`exists_folner_interval` then chooses `R` past `sup_F M(g)` plus
`sup_F |h(g)|`, and `L > (2Q+1)/eps` with `Q = sup_F |h(g)|`, so that for every
`g` in `F` the translated interval overlaps the original in all but at most
`2Q` points: `|g.A ∆ A| <= 2Q < eps.L`.

## What this does not give

Nothing about soficity of the action.  Følner sets in the orbit space and the
injective equivariant orbit charts the near-action definition wants are
different data, which is why the
[archived blanket action-soficity question](artifacts/ascending-hnn-coset-action-sofic.md) stays open and
this claim is not a step toward it.  Nothing here needs `Gamma` residually
finite, sofic, or finitely generated either — the estimate is uniform in
`Gamma`.
