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
`C*_max(K)` is quasidiagonal** (`K` the locally-residually-finite kernel).  That clause was
isolated as a named hypothesis, exactly matching the Prop lane `ring-b-alg` was going to produce.
`ring-b-alg` landed it (`AmenableExtensionTrace.manuscriptPrintedLocallyRFCanonicalTraceQuasidiagonal`,
`origin/main` commit `d4e4c824a`), and this lane discharged every reduction against it: **every
printed statement in this lane's brief is now closed and unconditional.**  A second, reopened
task then added per-sentence carriers for `prop:clifford-locally-rf`'s printed proof (and Theorem
4's one-sentence proof), following the `NormalKazhdanPrintedRoute.lean` pattern; see §3 for the
sentence-to-lemma table.

## 1. Modules landed

| module | commit(s) | job count |
| --- | --- | --- |
| `GroupApproximation/Sofic/CliffordWitnessSoficPrinted.lean` | `433d886ce83de060ba00935d6b854953feb4e942` (statement + reduction), `171122f528a2307008001c971c6cbaa3ab8007fa` (discharge) | 4317, 4319 |
| `GroupApproximation/Manuscript/OneSidedMFRadical/AffineCliffordTrace.lean` | `fe47ff6982cd3df59d521eda4ec84cc947f04a23` (statement + reduction), `2b6a0fdcb5512f9f46a8cbeb4898974203f89240` (discharge) | 4323, 4325 |
| `GroupApproximation/Manuscript/OneSidedMFRadical/AmenableTraceTheorem.lean` | `55fca1029cef72f1aad6fe158d5b5c9c65af148e` (statement + reduction), `a978a2b191765773ef3ccd74ded7f348c9cb8325` (discharge) | 4324, 4326 |
| `GroupApproximation/Sofic/CliffordWitnessSoficSentences.lean` | (landing) | |

Note: a probe of `Sofic/CliffordWitnessSoficPrinted.lean` initially failed the audit macro
(`#audit_closed_axioms` on a theorem whose *stated* type is a bare arrow `A → B` is rejected as
"has a leading input" even though the value is closed) --- fixed by wrapping the reduction in a
named `def ... : Prop := A → B` first, matching the pattern already used by
`PropertyT/EJZIntegralReduction.lean`.  Also, before it landed,
`GroupApproximation/Analysis/LocallyRFQuasidiagonalTrace.lean` was visible in the shared local
tree (ring-b-alg's in-progress file) with exactly the expected
`PrintedLocallyRFCanonicalTraceQuasidiagonal` and a complete proof by inspection --- it was not
depended on until it actually landed on `origin/main`.

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

* `manuscriptCliffordLocallyRF : PrintedCliffordLocallyRF` --- **discharged, unconditional,
  closed.**  `ring-b-alg` landed `Analysis/LocallyRFQuasidiagonalTrace.lean`
  (`origin/main` `d4e4c824a`), and this theorem is exactly
  `manuscriptCliffordLocallyRFFromLocallyRFTraceQuasidiagonal AmenableExtensionTrace.manuscriptPrintedLocallyRFCanonicalTraceQuasidiagonal`.
  `prop:clifford-locally-rf` is now closed with no open hypothesis anywhere.

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
  `a = v1G`.
* `manuscriptAffineCliffordConclusions` --- **discharged, unconditional, closed.**  The seven
  conclusions at the concrete instance, applying
  `manuscriptAffineCliffordConclusionsFromLocallyRFTraceQuasidiagonal` to `ring-b-alg`'s landed
  theorem.
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
  unconditional reduction.
* `manuscriptAmenableNonquasidiagonalTrace` --- **discharged, unconditional, closed.**  The full
  printed existential of Theorem `thm:amenable-trace`, applying the reduction above to
  `ring-b-alg`'s landed theorem.  Theorem 4 is now closed with no open hypothesis anywhere.
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

## 3. Sentence-level carriers (`Sofic/CliffordWitnessSoficSentences.lean`)

Reopened task, directed by the lead: the census work order (`notes/nonmf-lane-reports/census.md`,
"work order for the remaining ~320 unassigned sentences") listed `prop:clifford-locally-rf`
(proof) as needing sentence wrappers.  Following `NormalKazhdanPrintedRoute.lean`'s pattern, one
`manuscriptSentence_<slug>` lemma per printed sentence that asserts a checkable fact, quoting the
sentence in its docstring, proved from already-landed declarations.  The current tex (§4
shortened since the census's "28" count) has 18 proof sentences for `prop:clifford-locally-rf`
plus the theorem's own one-sentence proof ("Apply Proposition `prop:clifford-locally-rf` to
`Γ̄`, `α`, and `a`.") --- 19 rows total in `metadata/NON_MF_SENTENCE_CENSUS.tsv` at label
`prop:clifford-locally-rf`, env `proof` (the census script anchors Theorem 4's short proof to the
same, nearest-preceding label).

| # | printed sentence (abbreviated) | lemma | note |
| --- | --- | --- | --- |
| 1 | "Reassociating the semidirect products yields `W≅K⋊ℤ`." | `manuscriptSentence_reassociation` | projected from `manuscriptCliffordLocallyRF`'s 1st conjunct |
| 2 | "For `n≥0`, write `Γ_n=t^{-n}Γt^n`..." | --- (`definition`) | the object is `(MappingTelescope.level α hα n).range`; no independent content |
| 3 | "Since `[Γ:α(Γ)]<∞`... so `Γ` is commensurated by `V`." | `manuscriptSentence_commensuration` | `MappingTelescopeFiniteOrbits.level_relIndex_ne_zero` + `exists_level_repr` + `.vertical_le_commensurator` |
| 4 | "Hence the stabilizer... every `Γ_n`-orbit in `X` is finite." | `manuscriptSentence_stabilizerAndOrbitFinite` | `MappingTelescopeFiniteOrbits.finite_verticalLevel_orbit` + orbit-stabilizer |
| 5 | "A finite subset of `K` involves only finitely many lamps..." | `manuscriptSentence_finiteSubsetOneLevel` | the `F.sup lvl` argument already inline in `shiftKernelFor_isLocallyResiduallyFinite` |
| 6 | "Let `Y` be the union of the `Γ_n`-orbits..." | --- (`definition`) | `Y`/`C_Y` are not named separately; see row 7 |
| 7 | "Then `Y` is finite and `Γ_n`-invariant, and the finite subset is contained in `C_Y⋊Γ_n`." | `manuscriptSentence_finiteInvariantSubgroup` | `CliffordLamp.exists_finite_invariant_clifford_subgroup` |
| 8 | "where `C_Y=⟨ε,c_y:y∈Y⟩` is finite by the normal form above." | `manuscriptSentence_finiteInvariantSubgroup` | same lemma as row 7 |
| 9 | "This semidirect product is residually finite." | `manuscriptSentence_semidirectResiduallyFinite` | `residuallyFinite_semidirectProduct_of_finite_range` |
| 10 | "Indeed, an element with nontrivial `Γ_n`-component survives in a finite quotient." | `manuscriptSentence_semidirectResiduallyFinite` | internal to the same lemma's own proof |
| 11 | "For a nontrivial element of `C_Y`, let `J` be the kernel of the action..." | `manuscriptSentence_semidirectResiduallyFinite` | `J = φ.ker` inside the same lemma |
| 12 | "The quotient `Γ_n/J` is finite, and the element has nontrivial image..." | `manuscriptSentence_semidirectResiduallyFinite` | same lemma |
| 13 | "Therefore every finitely generated subgroup of `K` is residually finite." | `manuscriptSentence_locallyResiduallyFinite` | projected from `manuscriptCliffordLocallyRF`'s 2nd conjunct |
| 14 | "Each finitely generated subgroup of `K` is residually finite and hence sofic." | `manuscriptSentence_fgSubgroupSofic` | `isSofic_of_isLEF isLEF_of_residuallyFinite` |
| 15 | "The group `K` is their directed union, and `W/K≅ℤ` is amenable." | `manuscriptSentence_quotientAmenable` | `SoficByAmenablePermanence.isAmenable_int`; "directed union" is structural |
| 16 | "Soficity passes to directed unions and to extensions with amenable quotient, so `W` is sofic." | `manuscriptSentence_wSoficMechanism` | `isSofic_of_locallyResiduallyFinite` + `SoficByAmenablePermanence.isSofic_int_semidirectProduct` |
| 17 | "Proposition `prop:clifford-self-embedding` shows that it is not MF." | `manuscriptSentence_notMF` | `CliffordWitnessDirectDefect.not_isOperatorMF` |
| 18 | "By Proposition `prop:locally-rf-by-z-trace`... quasidiagonal... amenable... not quasidiagonal." | `manuscriptSentence_traceConclusions` | projected from `manuscriptCliffordLocallyRF`'s last 3 conjuncts |
| 19 (thm 4) | "Apply Proposition `prop:clifford-locally-rf` to `Γ̄`, `α`, and `a`." | `manuscriptSentence_theorem4Application` | `manuscriptAffineCliffordConclusions` |

Nothing in this table depends on an open hypothesis; every lemma is proved outright. Rows 6/8 and
10--12 reuse the same lemma as their block's primary row rather than getting an artificial
separate lemma, matching `NormalKazhdanPrintedRoute.lean`'s own treatment of its one purely-naming
sentence.

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
