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
| `GroupApproximation/Sofic/CliffordLampNormalFormSplice.lean` | `061ac3afc53fc91e683e4626b95c6f7266bfd481` | 1194 |
| `GroupApproximation/Sofic/CliffordLampNormalForm.lean` | `7de6eb784972efa781a7a45fc9f8473e8761c570` | 1195 |
| `GroupApproximation/Sofic/CliffordConstructionSentences.lean` (update, spends the normal form) | `f9487757d200212b50764ab71fdf2f63225b91ef` | 2825 |

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

## 5. The concrete Clifford construction sentences (`Sofic/CliffordConstructionSentences.lean`)

Second reopened task, directed by the lead: three census pockets whose printed sentences
describe the *concrete* Clifford lamp construction (generators/relations, the `𝔽₂`-cocycle
argument, the order computation, the automorphism action) while the repository's route to the
same conclusions is the abstract `MarkedCompressionGroup`/`Ambient` model.  Checked
`Sofic/CliffordLampGroup.lean` (and the modules built on it) before writing anything: it already
realizes the printed construction essentially verbatim.  Landed `bf343f3b92aae39b729a68d37e9c8ab419d98bb1`, PROBE GREEN, 2823 jobs.

| # | pocket | printed sentence (abbreviated) | carrier | status |
| --- | --- | --- | --- | --- |
| 1 | preamble | "Let `Γ` be a countable group with property (T)... choose `a∈Γ∖α(Γ)`." | --- | `definition` (same `Γ,α,a` used throughout) |
| 2 | preamble | "Put `T_α=lim(...)`, `V=T_α⋊⟨t⟩`." | --- | `definition` (`T_α`=`Telescope α hα`, `V`=`Vertical α hα`) |
| 3 | preamble | "where `tgt^{-1}=α(g)`... `T_α=⋃_{n≥0}t^{-n}Γt^n`." | `manuscriptSentence_hnnExtension` | **unconditional**: `vertical_compress` + `exists_level_repr` |
| 4 | preamble | "Put `X=V/Γ`, the left-coset space." | --- | `definition` (`X`=`Cosets α hα`) |
| 5 | preamble | "The Clifford lamp group `Cl(X)` is the group with generators `ε`,`c_x` and relations..." | `manuscriptSentence_cliffordLampPresentation` | **unconditional**: `sign_sq`,`lamp_sq`,`sign_commute_lamp`,`commutator_lamp_lamp` (`CliffordLamp X := PresentedGroup (relators X)` realizes exactly this presentation) |
| 6 | preamble | "To see that `ε≠1`, fix a total order... let `E` be the `𝔽₂`-vector space... `B(f,g)=Σ_{x>y}f(x)g(y)`." | --- | `definition` (`E`=`X →₀ ZMod 2`, `B`=`crossing`) |
| 7 | preamble | "Since `B` is bilinear,... is a group law on `𝔽₂×E`,... central involution... `(0,δ_x)` involution... exactly one of `B(δ_x,δ_y)`,`B(δ_y,δ_x)`=1... commutator=`(1,0)`." | `manuscriptSentence_signedModelGroupLaw` | **unconditional**: `mul_def`, `modelSign_commute`+`modelSign_sq`, `modelLamp_sq`, `crossing_single_add_swap`, `modelLamp_commutator` |
| 8 | preamble | "So `ε↦(1,0)`, `c_x↦(0,δ_x)` defines a homomorphism `Cl(X)→𝔽₂×E`." | `manuscriptSentence_toModelHomomorphism` | **unconditional**: `toModel`, `toModel_sign`, `toModel_lamp` |
| 9 | preamble | "The relations let us write every element of `Cl(X)` as `ε^a c_{x1}...c_{xr}`..." | `manuscriptSentence_cliffordLampNormalForm` | **unconditional**: `CliffordLampNormalForm.toModel_bijective_printed`'s `RightInverse section' (toModel X)` half (`section'` builds exactly this word, `1` or `ε` times the ascending word over the support) |
| 10 | preamble | "...and this word maps to `(a,δ_{x1}+...+δ_{xr})`, so the expression is unique and the homomorphism is an isomorphism." | `manuscriptSentence_cliffordLampNormalForm` | **unconditional** (closed the gap this round): `CliffordLampNormalForm.toModel_bijective_printed` --- `toModel X : CliffordLamp X →* SignedModel X` is bijective, with explicit two-sided inverse `section'`; uniqueness is `Injective (toModel X)`, "isomorphism" is the bijection itself. See §6 for the proof. |
| 11 | preamble | "In particular,... order `2^{|Y|+1}`, so `Cl(X)` is countable and locally finite." | `manuscriptSentence_cliffordLampCountableLocallyFinite` (countable+locally-finite half only) | **split**: countability/local finiteness unconditional, via `Countable (CliffordLamp X)` and `isLocallyFiniteGroup_cliffordLamp` (`Sofic/CentralInvolutionFinite.lean`'s unrelated central-involution route). The exact order `2^{|Y|+1}` is still a **gap**: the normal-form bijection (row 10) makes the order computation possible, but the finite-subgroup-order corollary itself has not yet been drawn from it. |
| 12 | preamble | "The relations are invariant under permutations of `X`, so every permutation... induces an automorphism... fixes `ε`." | `manuscriptSentence_permutationAutomorphism` | **unconditional**: `permHom`, `permHom_apply_sign`, `permHom_apply_lamp` |
| 13 | preamble | "In this way `V` acts on `Cl(X)` through its action on `X`, and we put `W=Cl(X)⋊V`." | `manuscriptSentence_verticalActsOnLamp` | **unconditional**: `lampAction`, `lampAction_apply_lamp`, `lampAction_apply_sign`; `W` is `MarkedCompression.Ambient`, definitionally |
| 14 | `prop:clifford-self-embedding` | "Then `tct^{-1}` is the lamp at `tΓ` and `a(tct^{-1})a^{-1}` is the lamp at `atΓ`." | `manuscriptSentence_conjugatedLampsAtCosets` | **unconditional**: `conj_inl_lamp` (applied twice); `c`=`cAmbient`=the lamp at `rootCoset` |
| 15 | `prop:clifford-self-embedding` | "These cosets are distinct, because `tΓ=atΓ` would mean `a∈tΓt^{-1}=α(Γ)`." | `manuscriptSentence_movedCosetsDistinct` | **unconditional**: `moved_cosets_ne`, whose own proof runs exactly this contradiction |
| 16 | `prop:clifford-locally-rf` | "so that `α(v,A)=(2v,A)`." | `manuscriptSentence_alphaDoublesTranslation` | **unconditional**, but in a *different* (mathematically equivalent) concrete model: `Monsters/AffineSL3Doubling.lean`'s `Gamma = (Fin 3 → ℤ) ⋊ SL(3,ℤ)`, independent of `ExplicitLinearModel`/`gammaBar`'s six-generator presentation but already used by the *same* proof for the index-eight computation (`LiteralAffineRangeIndexEight.lean`'s `latticeDouble := AffineSL3Doubling.doubleMul`).  `alpha_left`/`alpha_right` are literally "`α(v,A)=(2v,A)`" (the module's own docstring quotes this). |

**One gap remains, row 11's order-formula half.**  Rows 9 and 10 (the normal-form/isomorphism
sentence) closed this round: `Sofic/CliffordLampNormalForm.lean` proves
`Function.Injective (toModel X)` (jointly with the already-known surjectivity, `Bijective`), via
an explicit inverse `section' : SignedModel X → CliffordLamp X` built from the finite-support
decomposition of `f : X →₀ ZMod 2` in ascending order --- see §6 for the construction and §6's
closing note for the landed result.  What is left for row 11: drawing the finite-subgroup-order
corollary `Nat.card (Subgroup.closure ({sign X} ∪ lamp X '' Y)) = 2 ^ (Y.card + 1))` from the now-
proved bijectivity, for finite `Y ⊆ X`, by transporting
`Fintype.card (ZMod 2 × {f : X →₀ ZMod 2 // f.support ⊆ Y})`.

## 6. Third reopened task: the normal-form proof (`toModel` injective) --- scoped, then built and landed

The lead asked for the normal-form theorem itself, following a specific route (an explicit
section `SignedModel X → CliffordLamp X`, a key lemma for right-multiplication by a generator,
and a closure induction).  Worked the route through completely by hand before writing any Lean,
confirmed it is mathematically correct, and found every piece of Mathlib/repository API it needs
--- no missing eliminator anywhere.  Attempted a first module
(`Sofic/CliffordLampNormalForm.lean`) covering the `ZMod 2`/sign-power arithmetic and the
"swap a lamp past a word" lemmas; even that easiest quarter needed real care with noncommutative
associativity rewriting.  Did not probe or land it (removed the scratch file; nothing landed this
round) --- a candid estimate of the *remaining* three-quarters, below, showed the total would run
well past the "few hundred lines" budget, so stopping here to report the route precisely, as
instructed, rather than spend an open-ended number of probe/fix cycles against that estimate.

**The route, in full, with the exact obstruction at each stage:**

1. **The section.** `wordOfList (l : List X) := l.foldr (fun x acc => lamp X x * acc) 1` and
   `wordOfSupport s := wordOfList (s.sort (· ≤ ·))`; `section' ⟨a,f⟩ := (if a=0 then 1 else sign X)
   * wordOfSupport f.support`. Straightforward.
2. **Swapping.** `lamp_mul_lamp_swap {x≠y} : lamp x * lamp y = sign * (lamp y * lamp x)`, derived
   from `commutator_lamp_lamp` plus the involution facts; then `lamp_mul_wordOfList` (a fresh lamp
   commutes past a list of other distinct lamps, picking up `sign ^ length`), by list induction
   using the swap lemma and `sign_commute_lamp`/`sign_commute` to walk the accumulated sign to the
   front.  Both are "small" in the sense of being self-contained, but every step is a
   noncommutative-group identity that has to be assembled by hand (`calc` + targeted `mul_assoc`
   rewrites) --- no `group`/`ring_nf`-style tactic closes them automatically once a hypothesis like
   `a*a=1` has to be *used*, not just generic associativity. Real, but genuinely small (my draft:
   ~70 lines, and it plausibly still has a bug in exactly this kind of rewrite --- not probed).
3. **Splicing a point into the sorted word --- the actual size driver.**  The key lemma is
   `wordOfSupport (insert x s) = sign ^ ((s.filter (x < ·)).card) * wordOfSupport s * lamp X x` for
   `x ∉ s`.  Proving it requires building the explicit spliced list `L := (s.filter (·<x)).sort
   (≤) ++ x :: (s.filter (x<·)).sort (≤)` and showing (a) `L.Nodup`, (b) `L.toFinset = insert x s`,
   (c) `L.Pairwise (≤)` (via `List.pairwise_append`, twice, plus per-element membership facts
   connecting the two filtered pieces), then invoking `List.toFinset_sort`'s uniqueness-of-sorted-
   permutation direction to conclude `(insert x s).sort (≤) = L`, and finally applying
   `lamp_mul_wordOfList` to move `lamp X x` from the middle of `wordOfSupport L` to the end.  Every
   piece of API needed exists (`List.toFinset_sort`, `List.pairwise_append`, `Finset.sort_toFinset`,
   `List.toFinset_append`) but assembling them is a genuine ~100--150 line development, not a
   one-line wrapper.
4. **The round trip, both directions.**  `toModel (section' m) = m` is the "easy" direction (unfold
   the group law on `SignedModel X` against the definition, an induction on `f.support` via
   `wordOfSupport_insert` from step 3) --- maybe 40--60 lines.  The hard direction,
   `section' (toModel g) = g` for every `g`, is where the induction principle has to be chosen
   carefully: the naive property `P(g) := section'(toModel g) = g` is **not** closed under
   multiplication (`P(g)`, `P(h)` do not obviously give `P(g*h)`, since `section'` is not a group
   homomorphism), so `mem_subgroup_of_sign_mem_of_lamp_mem`/`PresentedGroup.generated_by` cannot be
   applied to `P` directly --- this is the one place a naive reading of "closure induction on the
   generating set" fails.  The fix (no missing eliminator, just a different choice of induction
   target): prove instead `Q(h) := ∀ n, section' (n * toModel h) = section' n * h`, universally
   quantified over `n`.  `Q` genuinely *is* closed under multiplication and inverse (a two-line
   computation each, using that `toModel` is a homomorphism), holds at `1`, and holds at each
   generator by step 3's key lemma read as a statement about arbitrary `n`.  Packaging `{h | Q h}`
   as an actual `Subgroup` (proving `one_mem'`, `mul_mem'`, `inv_mem'` from the three facts just
   listed) and applying `mem_subgroup_of_sign_mem_of_lamp_mem` gives `Q(g)` for every `g`;
   specializing at `n = 1` gives `section' (toModel g) = g`.  This is conceptually clean but is
   itself another ~80--120 lines (the `Subgroup` bundling plus the `Q`-closure algebra).
5. **Wiring.** `Function.Bijective toModel` from the two round-trip identities, the order formula
   `Nat.card (Subgroup.closure ({sign X} ∪ lamp X '' Y)) = 2 ^ (Y.card + 1)` for finite `Y` by
   transporting `Fintype.card (ZMod 2 × {f : X →₀ ZMod 2 // f.support ⊆ Y})` --- another ~50--80
   lines connecting a subgroup-of-a-presented-group cardinality statement to the bijection.

**Total honest estimate: 500--800 lines**, not "a few hundred," concentrated almost entirely in
steps 3 and 4 (the sort-splicing combinatorics and the closure-induction bundling), neither of
which reduces to an existing lemma or a short calculation --- both are real, self-contained proofs
that would need their own careful construction and multiple probe/fix rounds against
associativity-heavy `calc` blocks (as directly demonstrated by step 2 above, the *smallest* piece,
already needing hand-verified `calc` chains rather than one-line automation).  No blocking
capability gap: every mathlib/repository lemma named above exists at the pin and was checked by
reading it, not guessed.

**Result: built and landed, as two modules, per the lead's authorization at the larger budget.**
`Sofic/CliffordLampNormalFormSplice.lean` (`061ac3afc53fc91e683e4626b95c6f7266bfd481`, PROBE GREEN,
1194 jobs) carries steps 2--3 above (`wordOfList`, the swap/commute lemmas, and the sort-splicing
key lemma `wordOfSupport_insert`) exactly as scoped.
`Sofic/CliffordLampNormalForm.lean` (`7de6eb784972efa781a7a45fc9f8473e8761c570`, PROBE GREEN, 1195
jobs) carries steps 1 and 4--5's bijectivity half: `section'`, `section'_mul_modelLamp` /
`section'_mul_modelSign` (the key right-multiplication lemma, step 4), `toModel_section'` (the easy
round trip), the `Q`-closure induction (`satisfiesQ`, `qSubgroup`, `satisfiesQ_all`) giving
`section'_toModel` (the hard round trip), and `toModel_bijective` /
`toModel_bijective_printed`. Combined size ~615 lines (well within the 900-line stop-and-report
threshold), landing at the low end of the 500--800 line estimate since the order-formula corollary
(step 5's last piece) was deferred rather than attempted --- see the module's own docstring and
row 11 above.  `Sofic/CliffordConstructionSentences.lean` was then updated
(`f9487757d200212b50764ab71fdf2f63225b91ef`) to spend the theorem as
`manuscriptSentence_cliffordLampNormalForm`, closing rows 9 and 10.

The order formula (`2^{|Y|+1}`, row 11's remaining half) is not built: an early attempt at
characterizing `Subgroup.closure ({sign X} ∪ lamp X '' Y)` set-theoretically stalled, and rather
than force it past the point of diminishing returns, the incomplete draft was cut from the module
before landing --- nothing unproved was ever committed --- and it stands as the one open item,
per §5's gap paragraph above.
