---
rg: 2
id: ucp-hs-transport-kills-literal-mark
kind: claim
title: Unital completely positive Hilbert--Schmidt models of the literal group kill the central mark
distinct_from:
  literal-central-mark-corona-invisible: that is the operator-norm statement, proved in the tree; this asks the same conclusion for u.c.p. models that are only Hilbert--Schmidt asymptotically multiplicative, which is strictly harder and known to FAIL for merely bounded models because E is sofic.
artifacts:
  - GroupApproximation/Manuscript/NinetyNineProblems/KazhdanQuasidiagonalTraces.lean
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
---

For every sequence of u.c.p. maps `φₙ : C*(E) → M_{kₙ}` with
`‖φₙ(ab) − φₙ(a)φₙ(b)‖₂ → 0` and `tr ∘ φₙ → τ_E`, necessarily
`tr φₙ(u_w) → 1` for the central mark `w ≠ 1`.  Since `τ_E(u_w) = 0`, this is
the same as: no such sequence exists, i.e. `τ_E` is not amenable.

## Why u.c.p. could succeed where bounded fails

`E` is sofic, so BOUNDED Hilbert--Schmidt models exist
(`canonicalMaximalTrace_isHyperlinearTrace_of_isSofic`) and do NOT kill the
mark; any proof here must use complete positivity.  The one tool that does is
Kirchberg's lemma (Brown, Mem. AMS 184 (2006), Lemma 4.1.11, from Kirchberg
Math. Ann. 299 (1994)): for a Kazhdan group `K`, u.c.p. Hilbert--Schmidt
asymptotically multiplicative maps on `C*(K)` are trace-close to HONEST
finite-dimensional representations.  The base `B` of `E` (the six-generator
Kazhdan--Clifford group) has property (T), so on `C*(B)` the model is
character-close to honest representations `πₙ`, and the compression relations
`t vᵢ t⁻¹ = vᵢ²` make `φₙ(u_t)` a Hilbert--Schmidt approximate intertwiner
between the doubling twist of the base representation and its restriction.

## What has to be overcome

Kirchberg's lemma gives closeness of CHARACTERS, not of the models pointwise;
the manuscript's transport (`Sofic/LiteralNonMFEndpoint.lean`,
`kazhdanPinning`, `negativeCorner_kazhdanTransport_contradiction`) consumes
operator-norm control to build the conjugation representation, and the printed
remark (`manuscriptFullRadicalsDoNotEntailNonsoficity`) records that
Hilbert--Schmidt approximations do not supply it.  So the open question is
exactly whether property (T) plus complete positivity recovers enough of the
transport: (i) upgrade character-closeness on `B` to corner-wise unitary
conjugacy of honest representations (a second use of (T), on `π ⊗ π̄'`
approximate invariant vectors); (ii) run the doubling/Clifford sign count on
the large corner; (iii) control the lamp `c` and the mark
`w = [tct⁻¹, v₁ (tct⁻¹) v₁⁻¹]` there.  Step (ii) is where the sofic
block-tower models must, and do, escape: they are not u.c.p., and their
corners are permutation corners on which the Clifford sign is invisible.

Open in both directions; failure of (i)-(iii) is not evidence for
`literal-group-factorization-property` either.

The absolute (T) case is now typed and consumed:
`KirchbergKazhdanQuasidiagonalInput` (Brown Lemma 4.1.11 / Prop 4.1.12) in
`GroupApproximation/Manuscript/NinetyNineProblems/KazhdanQuasidiagonalTraces.lean` yields `problemX1_restricted_to_kazhdan` and
`not_hasFactorizationProperty_of_kazhdan_not_operatorMF`.  What this claim
asks beyond it is exactly the RELATIVE version: running the rigidity of the
Kazhdan base of `E` through models of the whole non-Kazhdan group.
