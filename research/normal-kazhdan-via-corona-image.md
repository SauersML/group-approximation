---
rg: 2
id: normal-kazhdan-via-corona-image
kind: route
title: The printed corona-image road to the normal-Kazhdan obstruction
target: normal-kazhdan-defect-non-mf
requires: []
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Sofic/CoronaImageNormalKazhdan.lean
---

## Why sufficient

A **second** complete proof of the same target, run along the manuscript's own
decomposition instead of the repository's more general one.  It changes no
status; it closes a route-level mismatch.

`thm:normal-kazhdan` is printed as a proof by contradiction along one specific
chain, and the existing route
[[normal-kazhdan-defect-non-mf-proof]] does not travel it:
`KazhdanCompressionCore.normalKazhdan_le_normMFResidual` proves a *stronger*
statement — membership in the universal norm-MF residual, quantified over
every operator-norm matrix ultraproduct — and reaches the corona conclusion
afterwards through the operator-MF/weak-MF abstraction layer.  That theorem is
correct and stays where it is.  This route is the printed chain, one Lean lemma
per printed link:

1. **`nk_01_surviving_corona_representation`** — a corona representation
   `Theta` surviving on `K` is passed to its coordinate model in the
   unitary-sequence corona (`lem:unitarycorona`);
2. **`nk_02_countable_mf_image`** — the image `H-bar = Theta(H)` is countable,
   hence MF.  Countability of the ambient `H` is exactly the manuscript
   hypothesis "let `H` be a countable group", and it is what makes the image
   countable here and supplies the exhaustion in the next step;
3. **`nk_03_separated_finite_models`** — `prop:mf-equivalences`, applied along
   an exhaustion of `H-bar`, yields an operator-norm asymptotic representation
   `(V_{g,n})` with separation `1` for fixed nontrivial elements: separated
   finite models;
4. **`nk_04_moving_corner`** — the moving corner built on those models
   contradicts the Hilbert--Schmidt invisibility of the image defect subgroup.

`nk_05_assembly` runs the contradiction, and
`manuscriptNormalKazhdanObstructionViaCoronaImage` states the conclusion in
the manuscript's literal natural-dimension corona language: for `C` a
`KazhdanCompressionCore` over a countable `H`, `K` normal with property (T)
and `K <= C.defectNormal`, and any dimensions `d_n > 0`, every
`Theta : H ->* unitary (NormMatrixCStarCorona (M_{d_n}))` kills `K`
elementwise.  The hypotheses are the printed ones and no more: no finiteness,
centrality, or torsion on `K`, and countability of the Kazhdan source carried
but unused, exactly as in print.

## What is reused rather than reproved

Step 4 is the existing `InternalRadicalGap` moving-corner machinery.  It is
*driven differently* here — directly by the separated models produced in step
3, rather than by a re-derived weak-MF predicate — but the corner calculation
itself is not duplicated.  That is the correct division: the printed proof and
the general theorem genuinely share their analytic core, and the thing that
differed was the route into it, which is what this node records.
