---
rg: 2
id: binary-leavitt-unit-group-is-f2-linear-sofic
kind: claim
title: The binary Leavitt unit group is linear sofic over F_2
distinct_from:
  non-linear-sofic-group: that asks for some group that is not linear sofic over some field; this asks that one specific group be linear sofic over F_2, which would make it no such witness in characteristic two and would settle Kaplansky positively for it.
  openai-leavitt-unit-nonsofic: that is nonsoficity of the same group in the Hamming metric; this is the rank-metric approximation property, which nonsoficity does not exclude.
artifacts:
  - research/artifacts/leavitt-inverse-defect-normal-forms-2026-09-12.md
  - research/artifacts/rank-row-compression-audit-2026-09-12.md
---

**OPEN.** `R^x`, with `R = L_(F_2)(1,2)`, is linear sofic over `F_2` in the sense of
Arzhantseva--Paunescu: finite subsets admit maps into `GL_n(F_2)` that are almost
multiplicative in normalized rank distance and keep every nontrivial element a
fixed rank distance from the identity.

Payoff: by `linear-sofic-group-algebra-is-stably-finite`, `F_2[R^x]` is stably
finite. So `leavitt-unit-group-algebra-is-directly-finite` holds, both lifting
problems of `leavitt-inverse-defects-are-visible-or-invisible` die, and every
injective `F_2`-linear automaton over `R^x` is surjective. In the other direction,
a Kaplansky pair in `F_2[R^x]` refutes this claim
(`non-linear-sofic-via-leavitt-kaplansky-failure`).

## Attempts

* **Through soficity.** Dead. Sofic groups are linear sofic, but `R^x` is nonsofic
  (`openai-leavitt-unit-nonsofic`).
* **Genuine representations.** Dead. `R^x` is finitely generated, simple and infinite,
  so every finite-dimensional linear representation of it is trivial. Approximations
  must be genuinely almost multiplicative.
* **Rank-metric compression rigidity (2026-09-12).** The rank row
  `f2-linear-sofic-groups-kill-rigid-compression-defects` would refute this claim through
  `non-linear-sofic-via-f2-rank-row-defect`.
  * Its linear-scale layer is established and too coarse
    (`rank-ultraproduct-compressors-conserve-fixed-right-ideals`,
    `linear-scale-rank-conservation-does-not-kill-defects`).
  * Below linear scale, the Hamming proof fails in the rank metric at two steps:
    rounding into expanding pieces, and one-piece transport, where compressors can rotate
    multiplicity coordinates (`research/artifacts/rank-row-compression-audit-2026-09-12.md`,
    Section 3).
  * Even the existence of a non-linear-sofic group over `F_2` is open.
* **Necessary condition on models.** Every rank model `sigma` of `R^x`, over any field,
  has `Fix^(a,b)(sigma(Gamma)) = Fix^(a,b)(sigma(R^x))` for the nine-leaf Kazhdan subgroup
  in every tensor degree (`leavitt-rank-models-kazhdan-fixed-ideals-are-global`). A
  construction where `Gamma` fixes, or commutes with, a linear-size piece that `R^x` does
  not is excluded.
* **Natural Cantor truncation.** Dead: length-changing prefix replacements lose rank
  (recorded on `f2-linear-sofic-groups-kill-rigid-compression-defects`).
