---
rg: 2
id: involutive-collapse-formalized-proof
kind: route
title: The involutive collapse is machine-checked end to end
target: involutive-compression-collapse
requires: []
artifacts:
  - GroupApproximation/Sofic/InvolutionCollapseEndpoint.lean
  - notes/COMPRESSION_COLLAPSE_MF_RADICAL.md
---

# The involutive collapse is machine-checked end to end

Direct establishment for the involutive lamp class `k² = 1` (the class
containing every application through involutions of the finite lamp
group, e.g. `A₅`).  `requires: []` is a proof commitment: every input is
an in-repo theorem.

The Lean chain (all modules imported by the root, no `sorry`, no axioms,
no literature inputs):

* exact commuting involution lifts with linear correction bounds
  (`ExactInvolutionLifts.exists_isExactInvolution_comm_of_unitary`) —
  this **establishes the `m = 2` case of
  [[corona-commuting-torsion-lifts]]**;
* corrected orbit microstates by diagonal extraction over a countable
  source (`InvolutionOrbitMicrostates.exists_involutionMicrostates`);
* the rank displacement metric, word bound, normalized displacement
  vectors with exact mass anchor `Σ = 4`, and marked positivity
  (`InvolutionCollapseMetric`, `InvolutionCollapseProfile`);
* the stagewise coboundary defect and the hyperreal standard-part
  transfer (`InvolutionCollapseCocycle`), feeding
  `UltralimitGaussian.profile_bounded_of_isKazhdanPair` — the
  Shalom-style Gaussian route through the in-repo Delorme theorem; this
  **establishes [[kazhdan-coboundary-collapse]]** without any
  ultraproduct space: sequence-level circumcenters
  (`Kazhdan.ApproximateCircumcenter`, `InvolutionCollapseCenter`)
  produce the approximate primitive directly;
* the one-stage Kazhdan corner transport
  (`InvolutionCollapseIndexCapture` + `transported_displacement_le`)
  contradicts the mass anchor of a marked model:
  `InvolutionCollapseEndpoint.no_marked_model`.

Corona conclusions: `coronaMFInvisible_commutator`,
`actualCoronaMFInvisible_commutator`, and the discharged endpoints
`actualCoronaMFInvisible_of_involutiveWitness`,
`involutiveCollapseDefect_le_actualCoronaMFResidual`,
`actualCoronaMFResidual_eq_comap_involutive_quotient` — all
unconditional.  The general `m > 2` witness class remains gated on
[[corona-commuting-torsion-lifts]] for `m > 2` only.
