# Formalization record: the marked-compression non-MF theorem

Date: 2026-08-12.

> **Historical formalization snapshot.** This file records the earlier
> Shalom-cover endpoint and the then-open literal-certificate boundary.  It is
> superseded for current status by the README, the generated numbered-claim
> manifest, and `non_mf_groups_exist.tex`.

This document records the proof architecture and audit surface of the completed
Lean formalization. It supersedes the development-time workstream plan; there
is no remaining `MarkedCompressionKill.lean` placeholder and the finitely
presented endpoint is not deferred.

## Headline declarations

The public theorem module is
`GroupApproximation/Sofic/ChosenNonMFTheorem.lean`. It exports:

```lean
ChosenNonMFTheorem.mark_normMFInvisible
ChosenNonMFTheorem.chosenFinitelyPresented_not_isWeakMF
ChosenNonMFTheorem.chosenFinitelyPresented_not_isOperatorMF
ChosenNonMFTheorem.countableWitness_not_isWeakMF
ChosenNonMFTheorem.countableWitness_not_isOperatorMF
ChosenNonMFTheorem.exists_countable_not_isWeakMF
ChosenNonMFTheorem.exists_finitelyPresented_not_isWeakMF
ChosenNonMFTheorem.exists_finitelyPresented_not_isOperatorMF
```

In particular, Lean proves both that the chosen nontrivial mark belongs to the
operator-norm MF residual and that a finitely presented non-MF group exists,
including `¬ IsOperatorMF` for the standard unitary-sequence presentation of
the cofinite corona.  `Analysis/NormMatrixCorona.lean` now constructs the
genuine C-star quotient, `Analysis/NormMatrixCoronaUnitary.lean` proves the
polar-correction isomorphism of unitary groups, and
`Sofic/CDEOperatorMF.lean` proves that the literal countable CDE definition is
equivalent to `IsOperatorMF`.
The finitely presented Lean witness is the independently constructed marked
group in `ChosenMarkedPresentation.lean`, whose vertex uses a
noncomputably chosen Shalom Kazhdan cover; it is not asserted to be
definitionally identical to the eight-generator presentation displayed in the
paper.

The universal analytic statement is:

```lean
MarkedCompressionInclusionData.word_normMFInvisible
```

For every countable group carrying the marked-compression inclusion data, its
marked word is killed by every homomorphism to every operator-norm matrix
ultraproduct. Together with nontriviality of the word, this gives:

```lean
MarkedCompressionInclusionData.not_isWeakMF
MarkedCompressionInclusionData.not_isOperatorMF
```

## Proof chain

The completed proof is split into independently useful layers.

1. `NormMFResidualDetector.lean` defines `NormMFInvisible`, the operator-norm
   MF residual, and proves that a nonidentity invisible element obstructs
   `IsWeakMF`.
2. `MarkedCompressionInclusionData.lean` packages the exact one-sided
   compression, central lamp, Kazhdan, and marked-word hypotheses. No
   injectivity or properness hypothesis is imposed on the analytic interface.
3. `ApproxInvolutionCorner.lean` and `NegativeCornerModel.lean` round the
   central approximate involution and
   pass to its nonzero negative corner. Renormalizing in the corner avoids any
   positive relative-rank assumption.
4. `AdjointMatrix.lean`, `KazhdanCompressorCorner.lean`,
   `ProjectionRankFlip.lean`, and `MarkedCompressionVectorChain.lean` build
   the adjoint Hilbert--Schmidt almost representation and implement the
   finite-stage Kazhdan pinning. The equal-rank projection flip is the
   finite-dimensional substitute for stable finiteness.
5. `MarkedCompressionSequentialKill.lean` proves that the marked commutator
   tends simultaneously to `1` in normalized Hilbert--Schmidt norm and to
   `-1` in operator norm, a contradiction. It then passes from arbitrary norm
   matrix ultraproducts to the sequential contradiction through
   `NormUltraproductSequentialExtraction.lean`.
6. `MappingTelescope.lean`, `CliffordLampGroup.lean`, and
   `MarkedCompressionGroup.lean` construct a countable witness and prove its
   marked word nontrivial.
7. `ChosenMarkedPresentation.lean` and `ChosenNonMFEndpoint.lean` provide a
   finite presentation selected noncomputably from a proved Shalom-cover
   existence theorem, with the same analytic interface and a nontrivial
   marked word. “Chosen” is essential: no printed relator list is extracted.
8. `OperatorMF.lean` extracts a sequential marked model directly from a mark
   surviving in the unitary-sequence presentation of the standard cofinite
   norm-matrix corona.
9. `ChosenNonMFTheorem.lean` joins the algebraic and analytic layers and
   publishes both the ultraproduct/weak-MF and unitary-sequence cofinite-corona
   endpoints.
10. `MarkedCompressionRootCapture.lean`, `FiniteNormalAverageCorner.lean`,
    and `FiniteNormalCompressionObstruction.lean` remove the distinguished
    central-involution hypothesis: every finite normal subgroup contained in
    the compression-defect normal closure lies in the norm-MF residual.
11. `LiteralNonMFPresentation.lean` and `LiteralNonMFLinearWitness.lean`
    machine-check the manuscript's literal eight-generator presentation and
    its exact nontrivial affine--Clifford mark.
    `LiteralBasePropertyTBridge.lean` proves from the printed affine relations
    that property `(T)` of the eight-relator rotation presentation implies
    property `(T)` of the literal base.  The public API deliberately contains
    no conditional analytic endpoint for the full group: property `(T)` of
    that rotation presentation has not been discharged, and no exact rational
    group-ring SOS certificate has been supplied.
12. `NormMFUniversalCorona.lean`, `NormMFCoronaRadical.lean`, and
    `NormMFResidualExactQuotient.lean` identify residual triviality with
    standard cofinite-corona operator MF and establish the universal quotient
    and exact factorization properties.
13. `NormMFPrintedConsequences.lean`, `OperatorMFPositiveControls.lean`, and
    `OperatorMFQuotientNonclosure.lean` package portability, uniform
    invisibility, positive permanence, and quotient nonclosure.
14. `FaithfulTracialMatrix.lean` and `ProperIsometryFromCompression.lean`
    isolate the matrix-trace and proper-isometry consequences used by the
    manuscript. `OperatorMFLocalNormalization.lean`,
    `MarkedGroupTopology.lean`, `MarkedGroupWordBall.lean`, and
    `MarkedMFClosed.lean` prove the normalized finite-model criterion,
    closedness of the fixed-rank marked MF locus, openness of its complement,
    and finite word-ball certificates. `MarkovMFConsequences.lean` provides
    explicitly conditional computability interfaces without asserting their
    external transformation data.
15. `Analysis/NormMatrixCorona.lean`,
    `Analysis/NormMatrixCoronaUnitary.lean`, `Analysis/MFAlgebra.lean`,
    `Sofic/CDEOperatorMF.lean`, `Sofic/CDEMFRadical.lean`, and
    `Sofic/MFDefinitions.lean` formalize the genuine C-star-corona target,
    the literal countable CDE predicate and radical, the MF-algebra notion,
    and the valid one-way implications from reduced/full/regular notions.

## What is and is not formalized

The Lean development machine-checks the universal marked-compression kill
theorem, the nontrivial marked witness, and countable and finitely presented
non-MF existence theorems. It separately proves the finitely presented
endpoint for the standard `IsOperatorMF` cofinite-corona predicate, without
assuming an equivalence with `IsWeakMF`. It does not claim that the finitely
presented Shalom-cover witness is literally the paper's displayed
eight-generator group. The literal group's algebraic presentation and
separating mark are formalized separately. No literal non-MF endpoint is
exported, even conditionally. The checked affine bridge reduces property
`(T)` of Lean's raw twenty-relator `PresentedGroup` to property `(T)` of its
eight-relator rotation retract. Known property `(T)` of the intended matrix
group does not discharge that premise without completeness of the rotation
presentation, an isomorphism, or a direct property-`(T)` proof. None of those,
and no exact certificate, is supplied by the unconditional endpoint. The
development also makes no claim that either witness is nonhyperlinear or
nonsofic.

`NormMFInvisible` quantifies over the repository's
`UniversalWeakMF U X`, namely operator-norm matrix ultraproducts over every
ultrafilter, including principal ultrafilters. This is a stronger target
family than the sequential `c_0` corona used in the paper's definition, not a
definitionally identical radical. For countable groups,
`coronaMFResidual_eq_normMFResidual` proves equality with the unitary-sequence
cofinite-corona radical, and `isOperatorMF_iff_normMFResidual_eq_bot` gives the
standard operator-MF bridge.  The stronger statement
`cdeMFResidual_eq_normMFResidual` now identifies both with the radical defined
directly through unitary groups of genuine norm-matrix C-star quotients.

## Audit surface

The public import path is:

```text
GroupApproximation.lean
  -> GroupApproximation/Endpoint/Public.lean
  -> GroupApproximation/Sofic/ChosenNonMFTheorem.lean
```

The focused audit target is
`GroupApproximation/Endpoint/ChosenNonMFAudit.lean`; it prints the axioms of
the chosen witness's invisibility theorem and both finitely presented non-MF
declarations, including `exists_finitelyPresented_not_isOperatorMF`. The same
declarations also appear in the project-wide endpoint and audit roster. No
`sorry`, custom axiom, or theorem-shaped literature premise is part of the
formal endpoint.

All Lean builds and audits for this project are run on MSI against the warm
cache. They are never run locally.
