---
rg: 2
id: atlas-true-criterion-baseline
kind: claim
title: The tensor flip meets the true criterion exactly on the cartesian escapees, and no classical start does better
distinct_from:
  atlas-steinberg-rank-five-translation: that established the usable list and hence the explicit criterion; this is the first exact evaluation of the criterion's landscape at its classical warm starts, the datum every analytic attack now starts from.
  atlas-kernel-window-length-nine: that is the finite-quotient obstruction (kernel words below length nine die under the retraction); this is its analytic shadow — the tensor flip's defect set on the true list is EXACTLY the retraction-escaping set — and the agreement of the two, reached from independent directions, is the content.
  leavitt-steinberg-hs-unstable: that is the open branch selection; this is a baseline computation about two specific unitaries, evidence for neither branch.
artifacts:
  - research/artifacts/atlas-true-criterion-probe-2026-08-15.md
  - experiments/atlas_true_criterion_warmstarts.py
---

For the explicit criterion of `atlas-steinberg-rank-five-translation`
(single unitary `U ∈ U(20160·k)`, the `T_St` relators evaluated in two
`U`-conjugate regular representations of `A₈`), the two classical
warm-start families evaluate in closed form at `k = 1` — every `π(s)` is
unitary, so `‖π(s) − I‖₂² = 2 − 2·Re tr π(s)`, and both families have
exact traces.

**Theorem (exact computation, full 4,636-relator list).**

1. **Automorphism alignments:** for every one of the 40,320 fold
   alignments, `tr π(s) ∈ {0, 1}` per relator and the maximum defect is
   `√2` — none kills the whole list (the fold screen already refuted
   that), so the entire classical sector is maximally bad in max-norm
   and only RMS distinguishes its members.
2. **Tensor flip `J`:** the defect is supported on **exactly the 72
   relators escaping `ker(A₈ * A₈ ↠ A₈ × A₈)`**, and equals exactly
   `√2` on each (the two projections are non-conjugate — one trivial,
   one a transvection — so the trace vanishes with no partial
   cancellation); RMS `= √(2·72/4636) = 0.176242`.  All 72 are
   Steinberg-product relators; the 24 involutivity relators are already
   exactly satisfied at `J`.

**Why this matters.**  The analytic objective and the finite-quotient
obstruction of `atlas-kernel-window-length-nine` agree exactly: the
tensor flip is precisely as good as the retraction theorem predicts and
not one relator better.  Consequently the **active set of the analytic
campaign is determined, not chosen** — the 72 cartesian escapees, an
86-fold cost reduction over the full list — with the 4,564
already-satisfied relators as a control that deformations must not
break.  Two traps for the optimizer are on record in the artifact: the
max-norm landscape is exactly flat between the classical starts (both
sit at `√2`; use the RMS or smoothed objective), and a Hutchinson trace
estimator has non-vanishing variance exactly at the criterion's regime
(use the residual estimator, whose variance vanishes at the optimum).
The staged plan — index-15 coset deformation first (1,344 identical
15×15 blocks, three orders cheaper), unrestricted `U` on the active set
second, `k`-trend last — with the measured cost wall (180,716
`U`-applications per full evaluation; unrestricted full-list `U(20160)`
is three to four orders out of reach) is the artifact's §(d).  All of
this is evidence-and-structure machinery, never proof in either
direction; monomial drift is a known descent trap, not progress.

**Stage 1 of that plan is now dead (2026-08-16).**  The index-15 coset
deformation is not merely a cheap first stage that failed to descend — it
cannot succeed at any multiplicity.  `atlas-stabilizer-commutant-no-go`
shows the family forces the exact relation `[π₁(m), π₂(b)] = 1` for `m`
in the stabilizer, which kills a word with nontrivial image in `Q`, and
quasisimplicity of `P̄/⟨⟨T_St⟩⟩` does the rest;
`atlas-stabilizer-slice-stationary` shows the first derivative at `J`
vanishes identically along the slice, so the flat MSI pilot was
structural rather than an under-optimized run.  The lane is recorded as
the invalidated route `atlas-stabilizer-coset-witness`.  What survives of
§(d) is stage 2 (unrestricted `U` on the active set) and stage 3 (the
`k`-trend, now constrained by `atlas-defect-gap-limit`: no isolated magic
multiplicities), plus one new cheap screen — evaluate the relations an
ansatz *forces* in the binary-Leavitt normal form before spending
anything on optimizing it.
