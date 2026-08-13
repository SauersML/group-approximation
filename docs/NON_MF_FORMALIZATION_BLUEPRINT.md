# Formalization record: the marked-compression non-MF theorem

Date: 2026-08-12. Status: **COMPLETE for the unconditional Shalom-cover
endpoint**; the literal eight-generator endpoint remains at the exact
property-`(T)`/rational-SOS certificate boundary described below.

This document records the proof architecture and audit surface of the completed
Lean formalization. It supersedes the development-time workstream plan; there
is no remaining `MarkedCompressionKill.lean` placeholder and the finitely
presented endpoint is not deferred.

## Headline declarations

The public theorem module is
`GroupApproximation/Sofic/ExplicitNonMFTheorem.lean`. It exports:

```lean
ExplicitNonMFTheorem.mark_normMFInvisible
ExplicitNonMFTheorem.chosenFinitelyPresented_not_isWeakMF
ExplicitNonMFTheorem.chosenFinitelyPresented_not_isOperatorMF
ExplicitNonMFTheorem.countableWitness_not_isWeakMF
ExplicitNonMFTheorem.countableWitness_not_isOperatorMF
ExplicitNonMFTheorem.exists_countable_not_isWeakMF
ExplicitNonMFTheorem.exists_finitelyPresented_not_isWeakMF
ExplicitNonMFTheorem.exists_finitelyPresented_not_isOperatorMF
```

In particular, Lean proves both that the chosen nontrivial mark belongs to the
operator-norm MF residual and that a finitely presented non-MF group exists,
including `¬ IsOperatorMF` for the standard unitary-sequence presentation of
the cofinite corona.  The polar-correction isomorphism to the unitary group of
the C-star quotient is a mathematical bridge, not a Lean declaration.
The finitely presented Lean witness is the independently constructed marked
group in `ExplicitMarkedPresentation.lean`, whose vertex uses a
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
7. `ExplicitMarkedPresentation.lean` and `ExplicitNonMFEndpoint.lean` provide
   an independently checkable finite presentation with the same analytic
   interface and a nontrivial marked word.
8. `OperatorMF.lean` extracts a sequential marked model directly from a mark
   surviving in the unitary-sequence presentation of the standard cofinite
   norm-matrix corona.
9. `ExplicitNonMFTheorem.lean` joins the algebraic and analytic layers and
   publishes both the ultraproduct/weak-MF and unitary-sequence cofinite-corona
   endpoints.
10. `MarkedCompressionRootCapture.lean`, `FiniteNormalAverageCorner.lean`,
    and `FiniteNormalCompressionObstruction.lean` remove the distinguished
    central-involution hypothesis: every finite normal subgroup contained in
    the compression-defect normal closure lies in the norm-MF residual.
11. `LiteralNonMFPresentation.lean` and `LiteralNonMFLinearWitness.lean`
    machine-check the manuscript's literal eight-generator presentation and
    its exact nontrivial affine--Clifford mark. `LiteralBaseSOS.lean` and
    `LiteralKazhdanCompression.lean` expose two honest conditional endpoints:
    property `(T)` of the literal base, or an exact rational group-ring SOS
    certificate implying it. Neither premise is postulated or discharged.
12. `NormMFUniversalCorona.lean`, `NormMFCoronaRadical.lean`, and
    `NormMFResidualExactQuotient.lean` identify residual triviality with
    standard cofinite-corona operator MF and establish the universal quotient
    and exact factorization properties.
13. `NormMFPrintedConsequences.lean`, `OperatorMFPositiveControls.lean`, and
    `OperatorMFQuotientNonclosure.lean` package portability, uniform
    invisibility, positive permanence, and quotient nonclosure.
14. `FaithfulTracialMatrix.lean` and `ProperIsometryFromCompression.lean`
    isolate the matrix-trace and proper-isometry consequences used by the
    manuscript. `MarkedGroupTopology.lean` and
    `MarkovMFConsequences.lean` provide reusable topology and explicitly
    conditional computability interfaces without asserting their external
    transformation data.

## What is and is not formalized

The Lean development machine-checks the universal marked-compression kill
theorem, the nontrivial marked witness, and countable and finitely presented
non-MF existence theorems. It separately proves the finitely presented
endpoint for the standard `IsOperatorMF` cofinite-corona predicate, without
assuming an equivalence with `IsWeakMF`. It does not claim that the finitely
presented Shalom-cover witness is literally the paper's displayed
eight-generator group. The literal group's algebraic presentation and
separating mark are formalized separately. Its non-MF theorem is available
only with an explicit property-`(T)` premise or an exact rational SOS
certificate; neither is supplied, chosen, or assumed by the unconditional
endpoint. The development also makes no claim that either witness is
nonhyperlinear or nonsofic.

`NormMFInvisible` quantifies over the repository's
`UniversalWeakMF U X`, namely operator-norm matrix ultraproducts. This is a
stronger target family than the sequential `c_0` corona used in the paper's
definition, and the sequential extraction layer is where the countability
hypothesis enters.

## Audit surface

The public import path is:

```text
GroupApproximation.lean
  -> GroupApproximation/Endpoint/Public.lean
  -> GroupApproximation/Sofic/ExplicitNonMFTheorem.lean
```

The focused audit target is
`GroupApproximation/Endpoint/ExplicitNonMFAudit.lean`; it prints the axioms of
the chosen witness's invisibility theorem and both finitely presented non-MF
declarations, including `exists_finitelyPresented_not_isOperatorMF`. The same
declarations also appear in the project-wide endpoint and audit roster. No
`sorry`, custom axiom, or theorem-shaped literature premise is part of the
formal endpoint.

All Lean builds and audits for this project are run on MSI against the warm
cache. They are never run locally.

## Credit and provenance

The proof files contain theorem-level credit for the closest mathematical
antecedents: Slofstra--Vidick for negative-eigenspace compression, Slofstra
for Clifford signs with shift/HNN machinery, Dadarlat's Lemma 3.18 and
Proposition 3.19 for the operator-norm to Hilbert--Schmidt property-(T)
lineage, Bachner--Dogon--Lubotzky Lemmas 2.2--2.3 and Propositions 1.5 and
2.4 for operator-norm involution rounding, corner-size renormalization, and
polar-corrected compression, and OpenAI Proposition 2.3 and Kun--Thom for
one-sided compressors and fixed-space propagation.

The Lean proofs in this repository were written for this project. No Physlib,
LeanQuantum, QECLean, or other external Lean source was copied. If external
code is adopted later, its license and source-level attribution must be
recorded in the importing file and repository notices before it is merged.
