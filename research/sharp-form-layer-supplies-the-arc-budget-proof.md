---
rg: 2
id: sharp-form-layer-supplies-the-arc-budget-proof
kind: route
title: Re-run the descent at lambda, keeping the positional core parameter-free
target: sharp-form-layer-supplies-the-arc-budget
requires: []
artifacts:
  - GroupApproximation/Sofic/GreendlingerSharpTwins.lean
  - GroupApproximation/Sofic/GreendlingerDeepVacuitySharp.lean
  - GroupApproximation/Sofic/GreendlingerLandingProd.lean
---

Machine-checked.

**The budget.**  A Greendlinger arc that survives three pieces retains
`1 - 3*lam` of the relator; `three_pieces_budget` proves the bound and
`three_pieces_budget_is_tight` shows no better constant follows from the same
count.  This is where `lam` enters, and it is the only place it needs to.

**The twins.**  `GreendlingerAtSharp` locates the sharp conclusion,
`LandsInSharp` and `CascadeLandingSharp` are the descent statements at `lam`,
and `sharpGreendlingerGate_of_cascadeLandingSharp` turns the descent into the
gate.  The deep and landing residuals twin as `DeepArcSourceSharp` and
`LandingProductionBetaSharp`, and
`cascadeLandingSharp_family_of_deepArcSharp_of_betaSharp` assembles them, so
the end state has exactly two hypotheses.

**The seam.**  `LocatedSplit` carries the positional content and takes no
`lam`.  Because of it, the sharp deep lane calls the *same* `not_deep_confined`
as the half lane (`deepArcSourceSharp_of_deepOverrunArcSharp`), so the emptiness
result of [[deep-two-factor-regime-is-empty]] was not duplicated.

**The necessity.**  `two_pieces_beat_the_half_form_witness` is a closed
arithmetic fact showing the half form fails at `lam = 1/8` on an explicit
length.  It is stated as a theorem rather than left in prose precisely so the
"why not just use the half form" question has a machine-checked answer.

## What this route does not do

It does not prove either sharp residual.  `LandingProductionBetaSharp` is
produced from `StoppingAlternativeBetaSharp`
(`landingProductionBetaSharp_of_stoppingAlternativeBetaSharp`), which is itself
open; `DeepArcSourceSharp` reduces to `DeepOverrunArcSharp`.  The layer's
achievement is that the sharp gate now has the same two-residual shape as the
half gate, so work on either lane transfers.
