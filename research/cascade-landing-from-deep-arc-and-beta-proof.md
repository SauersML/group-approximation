---
rg: 2
id: cascade-landing-from-deep-arc-and-beta-proof
kind: route
title: Plumb beta into landing production, then run the two-input descent
target: cascade-landing-from-deep-arc-and-beta
requires: []
artifacts:
  - GroupApproximation/Sofic/GreendlingerAlphaPlumb.lean
  - GroupApproximation/Sofic/GreendlingerBetaBranch.lean
---

Machine-checked.  Two steps.

**Plumbing.**  `landingProduction_of_beta` takes `MetricSmallCancellation R (1/6)`
and `LandingProductionBeta R` and returns `LandingProduction R`.  The metric
hypothesis is spent in one place, `landsIn_of_conjugatorAbsorbedSite`, which
reads the double piece bound; the module footer records that everything else on
the lane is unconditional apart from `C'(1/6)`.

`LandingProductionBeta` is the beta-branch form: it adds the decomposition
`M = E ++ invRev c` with `E` a suffix of the relator and `E` nonempty, and
crucially the negation `not ConjugatorAbsorbedSite c E M e`.  That negation is
what makes it a *branch* rather than a restatement --- the absorbed case is the
one the metric hypothesis closes directly.

**Descent.**  `cascadeLanding_of_deepArc_of_landing` takes `DeepArcSource R`
and `LandingProduction R` and returns `CascadeLanding R`, with no side
condition.  Composing gives `cascadeLanding_of_deepArc_of_beta`, and the
downstream gate is `greendlingerConclusion_of_deepArc_of_beta`.

## What a proof of either residual would have to do

`DeepArcSource` asks for a located arc in the regime where the block outruns
the conjugator.  Its two known reductions push it to `DeepTailArc` and to
`DeepOverrunArc`, and the second is worth taking because the two-factor case of
that regime is already **empty** ---
[[deep-two-factor-regime-is-empty]].

`LandingProductionBeta` asks for a landing in the non-absorbed branch.  Nothing
in the tree produces it; the sharp lane's analogue is produced from
`StoppingAlternativeBetaSharp`, so the same shape of reduction is presumably
available here, and would be the cheap next move.
