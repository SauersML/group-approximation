# Lane `thm-d`: Theorem 4, `prop:clifford-locally-rf`, the former `cor:affine-clifford-trace`

Date opened 2026-09-07.  Lane owner: session `thm-d` of the non-MF formalization campaign.
All declarations live in sub-namespace `GroupApproximation.AmenableTraceTheorem`.

## 0. One-paragraph summary

Theorem 4 (`thm:amenable-trace`), Proposition `prop:clifford-locally-rf`, and the former
corollary `cor:affine-clifford-trace` (merged by the tex owner into Theorem 4's own proof,
`origin/main` commit `e51f655d2`) were `paper-proof` in
`metadata/NON_MF_NUMBERED_CLAIMS.json` even though almost every clause was already proved in
Lean.  This lane assembled the exact printed carriers.  Mid-lane, `e51f655d2` generalized
`prop:locally-rf-by-z-trace` from a `⋊ ℤ` extension to a general amenable extension and added a
new clause to both it, `prop:clifford-locally-rf`, and Theorem 4: **the canonical trace of
`C*_max(K)` is quasidiagonal** (`K` the locally-residually-finite kernel).  That clause is not
yet in the repository; lane `ring-b-alg` is proving it in general as
`GroupApproximation.AmenableExtensionTrace.manuscriptPrintedLocallyRFCanonicalTraceQuasidiagonal`
in `Analysis/LocallyRFQuasidiagonalTrace.lean` (not yet landed).  Every other clause of every
theorem in this lane's brief is proved unconditionally.  The open clause is isolated as a named
hypothesis, exactly matching the Prop ring-b-alg will produce, so that landing their module
closes everything here in one line each (given below).

## 1. Modules landed

| module | commit | job count |
| --- | --- | --- |
| `GroupApproximation/Sofic/CliffordWitnessSoficPrinted.lean` | `433d886ce83de060ba00935d6b854953feb4e942` | 4317 |
| `GroupApproximation/Manuscript/OneSidedMFRadical/AffineCliffordTrace.lean` | `fe47ff6982cd3df59d521eda4ec84cc947f04a23` | 4323 |
| `GroupApproximation/Manuscript/OneSidedMFRadical/AmenableTraceTheorem.lean` | `55fca1029cef72f1aad6fe158d5b5c9c65af148e` | 4324 |

Note: a probe of `Sofic/CliffordWitnessSoficPrinted.lean` initially failed the audit macro
(`#audit_closed_axioms` on a theorem whose *stated* type is a bare arrow `A → B` is rejected as
"has a leading input" even though the value is closed) --- fixed by wrapping the reduction in a
named `def ... : Prop := A → B` first, matching the pattern already used by
`PropertyT/EJZIntegralReduction.lean`.  Also, `GroupApproximation/Analysis/LocallyRFQuasidiagonalTrace.lean`
already exists in the shared local tree (ring-b-alg's in-progress file, not yet on
`origin/main`) with exactly the expected `PrintedLocallyRFCanonicalTraceQuasidiagonal` and a
complete (no open obligation) `manuscriptPrintedLocallyRFCanonicalTraceQuasidiagonal` proof
visible by inspection --- not depended on here since it is not yet landed, but the one-line
discharge is expected to apply as soon as it is.

## 2. Declarations, by printed statement

### `prop:clifford-locally-rf` --- `Sofic/CliffordWitnessSoficPrinted.lean`

* `PrintedCliffordLocallyRF` --- the full printed Prop (7 conjuncts: the reassociation
  equivalence, local residual finiteness of `K`, soficity of `W`, `¬ IsOperatorMF W`,
  quasidiagonality of `K`'s canonical trace, amenability of `W`'s canonical trace, and
  non-quasidiagonality of `W`'s canonical trace), for a general countable Kazhdan group `Γ`, an
  injective finite-index self-embedding `α`, and `a ∉ range α`.
* `PrintedLocallyRFCanonicalTraceQuasidiagonal` --- the isolated open hypothesis: for a
  countable, locally residually finite group `N`, the canonical trace of `C*_max(N)` is
  quasidiagonal.  **This is `prop:locally-rf-by-z-trace`'s first assertion**, specialized to what
  `prop:clifford-locally-rf` consumes.  Chosen to match exactly what the lead reported
  ring-b-alg will produce:
  `GroupApproximation.AmenableExtensionTrace.manuscriptPrintedLocallyRFCanonicalTraceQuasidiagonal
  : PrintedLocallyRFCanonicalTraceQuasidiagonal` in `Analysis/LocallyRFQuasidiagonalTrace.lean`
  (`∀ (N : Type) [Group N] [Countable N], LocallyRFByIntAmenableTrace.IsLocallyResiduallyFinite N
  → Quasidiagonal.IsQuasidiagonalTrace (fun a : MaximalGroupCStar N ↦ canonicalMaximalTrace N
  a)`).  `exact`/defeq does not care which namespace declares an equal `def`, so the discharge
  below is genuinely one line once that module lands, whatever namespace it uses.
* `PrintedCliffordLocallyRFFromLocallyRFTraceQuasidiagonal := PrintedLocallyRFCanonicalTraceQuasidiagonal → PrintedCliffordLocallyRF`
  and `manuscriptCliffordLocallyRFFromLocallyRFTraceQuasidiagonal` --- **closed, unconditional**
  theorem proving the reduction.  `#audit_closed_axioms` passes because the open content sits
  inside the hypothesis type, not as a bare argument (an arrow spelled out directly in a
  theorem's stated type is rejected by the audit macro as "a leading input"; wrapping it in a
  named `Prop` is required and is the pattern already used by
  `PropertyT/EJZIntegralReduction.lean`).
* `isSofic_ambient_of_residuallyFinite` --- helper: `Ambient α hα` is sofic whenever `Γ` is
  residually finite and `α` has finite-index range, via `SoficMarkedCompression.isSofic_ambient`
  fed by `isSofic_of_isLEF isLEF_of_residuallyFinite`. Unconditional.

**Discharge, when `Analysis/LocallyRFQuasidiagonalTrace.lean` lands:**
```lean
theorem manuscriptCliffordLocallyRF : PrintedCliffordLocallyRF :=
  manuscriptCliffordLocallyRFFromLocallyRFTraceQuasidiagonal
    AmenableExtensionTrace.manuscriptPrintedLocallyRFCanonicalTraceQuasidiagonal
```

### The former `cor:affine-clifford-trace` --- `Manuscript/OneSidedMFRadical/AffineCliffordTrace.lean`

Kept as the named proof step it now is (the label itself no longer exists in the tex; the tex
owner merged its content into the proof of Theorem 4).

* `PrintedAffineCliffordHypotheses` and `manuscriptAffineCliffordHypotheses` --- **unconditional,
  closed**: `alpha.range.index = 8` (from
  `LiteralAffineRangeIndexEight.conjD_range_index_eq_eight`, already in the tree — this lane
  only had to find and cite it) and `v1G ∉ Set.range alpha` (from
  `ExplicitLinearModel.v1G_not_mem_range`, already in the tree).
* `PrintedAffineCliffordConclusionsFromLocallyRFTraceQuasidiagonal` and
  `manuscriptAffineCliffordConclusionsFromLocallyRFTraceQuasidiagonal` --- the concrete instance
  of `PrintedCliffordLocallyRFFromLocallyRFTraceQuasidiagonal` at `Γ̄ = gammaBar`, `α = alpha`,
  `a = v1G`.  Same one-line discharge shape as above, applied here.
* `manuscriptAffineCliffordConclusionsCore` --- **unconditional, closed**: the four conclusions
  that do not need the open clause (`WitnessGroup` sofic, `¬ IsOperatorMF WitnessGroup`, its
  canonical trace amenable, its canonical trace not quasidiagonal), assembled from
  `LiteralWitnessConsequences.witnessGroup_isSofic`,
  `LiteralWitnessConsequences.witnessGroup_not_isOperatorMF`, and
  `NinetyNineProblems.witnessCanonicalTrace_amenable_not_quasidiagonal` (all pre-existing).

### `thm:amenable-trace` --- `Manuscript/OneSidedMFRadical/AmenableTraceTheorem.lean`

* `PrintedAmenableNonquasidiagonalTrace` --- the full printed existential (7 conjuncts, same
  shape as `prop:clifford-locally-rf`, instantiated at `∃ W K`).
* `PrintedAmenableNonquasidiagonalTraceFromLocallyRFTraceQuasidiagonal` and
  `manuscriptAmenableNonquasidiagonalTraceFromLocallyRFTraceQuasidiagonal` --- closed,
  unconditional reduction, same one-line discharge shape.
* `manuscriptAmenableNonquasidiagonalTraceCore` --- **unconditional, closed**: the three
  conclusions not needing the open clause (the reassociation, `K` locally residually finite,
  `W` sofic and not operator-MF, `W`'s trace amenable and not quasidiagonal).
* `manuscriptShiftKernelIsOperatorMF` --- **unconditional, closed**.  First remark: "Since `K` is
  a direct limit of residually finite groups, it is MF", via
  `isOperatorMF_of_isLEF (isLEF_of_locallyResiduallyFinite shiftKernel_isLocallyResiduallyFinite)`.
* `manuscriptMFNotClosedUnderIntSemidirect` --- **unconditional, closed**.  Second remark: "MF
  groups are not closed under semidirect products with `ℤ`" --- `ShiftKernel` is operator-MF,
  `WitnessGroup ≃ ShiftKernel ⋊ ℤ` is not, via
  `CommensurabilityInvariance.isOperatorMF_of_mulEquiv` transported across
  `witnessGroupEquivShiftKernelByInt.symm`.
* `PrintedWSoficFromLocallyRFExtension` and `manuscriptWSoficFromLocallyRFExtension` ---
  **unconditional, closed**.  The soficity-mechanism sentence "the group `W` is sofic because
  locally residually finite groups are sofic and soficity passes to extensions with amenable
  quotient": for any `W ≃ K ⋊ ℤ` with `K` locally residually finite, `W` is sofic, via
  `SoficByAmenablePermanence.isSofic_int_semidirectProduct` (Elek--Szabó, Theorem 1) composed
  with `isSofic_of_locallyResiduallyFinite`.

## 3. What remains

The single open obligation, everywhere in this lane, is the same Prop:

```lean
def PrintedLocallyRFCanonicalTraceQuasidiagonal : Prop :=
  ∀ (N : Type) [Group N] [Countable N],
    LocallyRFByIntAmenableTrace.IsLocallyResiduallyFinite N →
      Quasidiagonal.IsQuasidiagonalTrace
        (fun a : MaximalGroupCStar N ↦ canonicalMaximalTrace N a)
```

owned by lane `ring-b-alg` (`Analysis/LocallyRFQuasidiagonalTrace.lean`,
`Analysis/AmenableExtensionAmenableTrace.lean`).  Once it lands, three one-line theorems close
every remaining printed endpoint in this lane (shown in each section above).  Nothing else in
this lane's brief is open.

## 4. Note on the ℤ-specific step (per the lead's 2026-09-07 heads-up)

The lead flagged that `prop:locally-rf-by-z-trace`'s amenable-trace-of-`G`-clause might one day
need generalizing from a `⋊ ℤ` extension to an arbitrary amenable-quotient extension.  The
carrier this lane uses for that clause,
`LocallyRFByIntFactorization.canonicalMaximalTrace_isAmenableTrace_of_locallyRFByInt`
(`Analysis/LocallyRFByIntFactorization.lean`), is exactly the ℤ-specific step: its height
function (`height`), cyclic level window (`stageLevelWindow`, `levelSize`), and boundary-ratio
estimate are all built for the integer shift and would need a Følner-tiling generalization to a
general amenable quotient.  The lead confirmed on 2026-09-07 that this carrier stays valid
as-is for this lane's amenability clause (`W`'s trace is amenable), since `W/K ≅ ℤ`
concretely — no action needed here unless the tex is changed to ask for the amenable-trace
clause at a base group other than `ℤ`.
