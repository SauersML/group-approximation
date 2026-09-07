# Lane `printed-route`: printed proofs of the rewritten normal-Kazhdan theorem

Lane brief: the manuscript's proofs of `thm:normal-kazhdan`, `thm:transport`
and `lem:central-corona-corner` were rewritten to avoid ultrafilters, so the
existing Lean carriers prove the exact printed *statements* by the old route
and no carrier follows the printed *sentences*.  This lane produces a second
proof of the same closed statement along the printed sentences, with
sentence-level lemmas the census can cite.

Read the printed proofs from `git show origin/main:non_mf_groups_exist.tex`;
the worktree copy is edited live by the tex owner.  As of 2026-09-07 the
committed tex contains **no** occurrence of "ultrafilter", "ultralimit" or
`\omega`: all three proofs are ultrafilter-free.

## Landed

### `Manuscript/OneSidedMFRadical/PrintedRouteAnalyticFacts.lean`

Commit `24919eb7d12801fb9de610a67a2385be58d8d1a0`, PROBE GREEN, 3293 jobs.
Sub-namespace `GroupApproximation.Manuscript.OneSidedMFRadical.NormalKazhdanPrintedRoute`.
The four analytic facts the rewritten proof spends that the tree carried only
in pieces:

| declaration | what it supplies |
| --- | --- |
| `blockExtend_zero` / `_add` / `_smul` | linearity of the zero extension |
| `cornerEmbed_zero` / `_add` / `_smul` / `cornerEmbed_sum_smul` | the corner embedding of `Analysis/CornerMatrixEmbedding` is linear (that file proves only `sub`, `mul`, `star`, isometry) |
| `coronaRestrictAlg`, `coronaRestrictAlg_mk`, `norm_coronaRestrictAlg_le` | the coordinate restriction of `CornerCoronaClass` as a `→⋆ₐ[ℂ]`, so it moves the complex coefficients `α_k`; `CornerCoronaClass.coronaRestrict` is only a `→+*` |
| `exists_generatorCombination_close` | density of `ℂ[K]` in `Cmax(K)` with the finite sum exhibited |
| `norm_normTrace_sub_one_le` | the printed `\|tr_r(u) − 1\| ≤ ‖u − I_r‖₂` |
| `normTrace_sum_smul` | the trace of a printed finite combination |

### `Manuscript/OneSidedMFRadical/NormalKazhdanPrintedRoute.lean`

Commit `ac979d6a603df33c25438b9dddba794cb9a640d0`, PROBE GREEN, 4131 jobs.
Endpoint:
`GroupApproximation.Manuscript.OneSidedMFRadical.NormalKazhdanPrintedRoute.manuscriptNormalKazhdanRadical_printedRoute : NormalKazhdanRadical`
with `#audit_closed_axioms` on it.  `NormalKazhdanRadical` is the *same* closed
proposition `Manuscript/OneSidedMFRadical/NormalKazhdan.lean` already carries;
the old carrier `manuscriptNormalKazhdanRadical` and the old sentence module
`NormalKazhdanSentences.lean` are untouched.

## Sentence to lemma table (`thm:normal-kazhdan`, current printed proof)

| printed sentence | carrier |
| --- | --- |
| "Let `e_K ∈ C*_max(K)` be the Kazhdan projection of `K`, and let `p ∈ 𝒬_d` be its image under the homomorphism `C*_max(K) → 𝒬_d` induced by `Θ\|_K`." | `manuscriptSentence_kazhdanProjectionImage` |
| "Since `gKg⁻¹ = K` ..." (both compression inclusions) | `manuscriptSentence_normalityGivesBothCompressions` |
| "In any faithful representation of the corona, `p` is the projection onto the `K`-fixed vectors ... so `Θ(g) p Θ(g)* = p`." | `manuscriptSentence_conjugateFixesKazhdanImage` |
| "... and `q = 1 − p` is nonzero because `Θ` is nontrivial on `K`." | `manuscriptSentence_complementNonzero` |
| "`q = 1 − p`" as a projection commuting with `Θ(G)` (the input `lem:central-corona-corner` consumes) | `manuscriptSentence_complementIsCentralProjection` |
| "By Lemma `lem:central-corona-corner` there is an operator norm asymptotic representation `W_n : G → U(r_n)` whose corona homomorphism `Θ̂` is the coordinate restriction of `g ↦ q Θ(g)`." | `manuscriptCornerCoronaClass` (existing carrier, `CornerCoronaClass.lean`) |
| "Since `q` commutes with `Θ(K)`, the map `a ↦ q Θ(a)` is a homomorphism on `C*_max(K)` agreeing with `π` on `K`, so `π(e_K)` is the coordinate restriction of `q p = 0`." | `manuscriptSentence_cornerCoronaKillsKazhdanProjection` |
| "The group algebra `ℂ[K]` is dense in `C*_max(K)`, so there are a finite set `F ⊆ K` and scalars `(α_k)` with `a = Σ α_k u_k`, `‖a − e_K‖ < 1/4`.  The trivial character `χ` ... has `χ(e_K) = 1`, so `\|Σ α_k − 1\| = \|χ(a − e_K)\| < 1/4`." | `manuscriptSentence_denseCombinationAndCharacter` |
| "Since `π(e_K) = 0`, `limsup_n ‖Σ α_k W_n(k)‖ = ‖π(a)‖ = ‖π(a − e_K)‖ < 1/4`." | `manuscriptSentence_limsupCombinationLtQuarter` (helper `sum_smul_ambientCornerSeq_apply`) |
| "The hypothesis applies to `(W_n)` itself, so `\|tr_{r_n}(W_n(k)) − 1\| ≤ ‖W_n(k) − I_{r_n}‖₂ → 0` ... and then `tr_{r_n}(Σ α_k W_n(k)) → Σ α_k`." | `manuscriptSentence_traceOfCombinationTendsTo` |
| "Since `\|tr_{r_n}(x)\| ≤ ‖x‖`, the limit has absolute value at most `1/4`, while `\|Σ α_k\| > 3/4`, a contradiction." | assembled in `manuscriptNormalKazhdanRadical_printedRoute`, from `PrintedPreliminaryEstimates.norm_normTrace_le_l2_opNorm` and `Filter.eventually_lt_of_limsup_lt` |

### One deliberate departure from the printed words

The printed sentence justifies `Θ(g) p Θ(g)* = p` through a faithful
representation of the corona and an equality of two fixed-vector subspaces.
No faithful representation is constructed here.  The Lean route proves the
same identity algebraically: `Analysis/MaximalCStarKazhdanProjection.lean`'s
`star_conj_image_mul_image` is one range inclusion and `conj_image_mul_image`
applied to `Θ(g)*` is the other, and normality is exactly what makes the
second available (`gKg⁻¹ = K` compresses `Θ(K)` by `Θ(g)` *and* by `Θ(g)*`).
One inclusion alone gives only `lem:kazhdan-projection-order`'s inequality
`Θ(g)* p Θ(g) ≤ p`.

The printed `π : C*_max(K) → 𝒬_r` is likewise not built as a separate
homomorphism into the corner corona: the printed chain
`limsup ‖Σ α_k W_n(k)‖ = ‖π(a)‖ = ‖π(a − e_K)‖ < 1/4` is carried by the corona
norm of the *coordinate restriction* of `q f(a)`, which is what
`CornerCoronaClass` already identifies with the class of the corner
combination.  The two readings differ only by the identification
`q 𝒬_d q ≅ 𝒬_r`, which the printed proof of `lem:central-corona-corner` makes
and which the corona norm makes unnecessary here.

### `Manuscript/OneSidedMFRadical/CornerCoronaEmbedding.lean`

Commit `333bf6f528d05c351e732f01c6509b27f8299be7`, PROBE GREEN, 3294 jobs.
The printed sentence "unitary identifications `J_n` identify each corner
`q_n M_{d_n}(C) q_n` with `M_{r_n}(C)`, and then the corner `q 𝒬_d q` with the
corona `𝒬_r`", which the tree carried only coordinatewise:

| declaration | what it supplies |
| --- | --- |
| `cornerEmbed_one`, `cornerEmbed_mem_corner` | completes the coordinatewise identification: `J_n 1 J_n* = q_n`, image of `J_n` is the corner |
| `cornerModel`, `cornerModel_nonempty`, `cornerModel_card_pos` | the corner as a finite matrix model, nonempty exactly at retained coordinates |
| `cornerEmbedSeq`, `cornerCompressSeq`, `cornerEmbedSeq_cornerCompressSeq_apply` | the two sequence-level maps and the printed representative `(q_n z_n q_n)` |
| `cornerEmbedSeq_mul` / `_sub` / `_star` / `_one_apply` | it is a star-embedding sending the corner unit to `(q_n)` |
| `norm_mk_cornerEmbedSeq`, `mk_eq_of_mk_cornerEmbedSeq_eq`, `mk_cornerEmbedSeq_congr` | the class of `(J_n c_n J_n*)` has the same norm as the class of `(c_n)`, so the passage is two-way |

### `Manuscript/OneSidedMFRadical/CentralCoronaCornerPrintedRoute.lean`

Commit `9091ae72eff1ddc537333cccbc871d8f9a797547`, PROBE GREEN, 3297 jobs.
Endpoint
`GroupApproximation.Manuscript.OneSidedMFRadical.CentralCoronaCornerPrintedRoute.manuscriptPrintedCentralCoronaCorner : PrintedCentralCoronaCorner`
with `#audit_closed_axioms`.

| printed sentence | carrier |
| --- | --- |
| "Lift `q` to projections `q_n` by functional calculus." | `CollapseProjectionLift.exists_projection_lift` (existing) |
| "Since `q ≠ 0`, infinitely many `q_n` are nonzero; retain those coordinates." | `manuscriptSentence_retainedCoordinatesInfinite` |
| "Unitary identifications `J_n` identify each corner with `M_{r_n}(C)`, and then the corner `q 𝒬_d q` with the corona `𝒬_r`." | `CornerCoronaEmbedding` (module above) |
| "Since `q` commutes with `ρ(G)`, `g ↦ q ρ(g)` is a homomorphism into the unitary group of the corner ... it lifts to unitaries `W_n(g)`, with `W_n(1) = I`. Multiplicativity in the corona makes `(W_n)` an operator norm asymptotic representation, and the class of `(J_n W_n(g) J_n*)` is the coordinate restriction of `q ρ(g)`." | `exists_cornerUnitaries` |
| the whole lemma | `manuscriptPrintedCentralCoronaCorner` |

`PrintedCentralCoronaCorner` is a *new* closed Prop, not the existing
`CentralCoronaCorner`.  The existing one is strictly stronger: it additionally
pins `D.V` to the polar-decomposition lifts of `ρ(g)` and states the corner
maps as polar corrections of the compressions `q_n V_n(g) q_n`, which is the
old route's data and does not appear in the printed lemma at all.  Both are
faithful readings of the printed *statement*; only the new one has a proof
that follows the printed *sentences*.  `CentralCoronaCorner.lean` and
`CornerCoronaClass.lean` are untouched.

`r_n = rank(q_n)` is not claimed by either statement: here `r_n` is the number
of retained corner coordinates and only `0 < r_n` is proved, exactly as the
existing carrier does with `0 < Fintype.card (D.cornerModel k)`.

### `Manuscript/OneSidedMFRadical/HilbertSchmidtAdMatrix.lean`

Commit `0e482802ff6ae4ff2560df65537831ebdfeb6e42`, PROBE GREEN, 3294 jobs.
The opening sentences of the rewritten `thm:transport` proof, in the
sub-namespace `HilbertSchmidtAdMatrix`.

| printed sentence | carrier |
| --- | --- |
| "The algebra `𝓑` is a norm matrix corona with coordinate sizes `d_n²` after a choice of matrix units." | `adMatrix` (the matrix of `x ↦ V x V*`, i.e. `V ⊗ V̄`), with `adMatrix_one`, `adMatrix_mul`, `adMatrix_conjTranspose`, `adMatrix_mem_unitary`; `unvec_adMatrix_mulVec` says its action is the printed `x ↦ V x V*` |
| "For unitaries `A, B`, `‖Ad(A) − Ad(B)‖ ≤ 2‖A − B‖`, where the norm on the left is the operator norm on the Hilbert space `(M_{d_n}(ℂ), ‖·‖₂)`" | `hsNormSq_conj_sub_conj_le` and `norm_adMatrix_sub_le` |
| the printed normalization `tr_d = d⁻¹ Tr` | `norm_sq_eq_card_mul_hsNormSq`: the Euclidean norm of a vectorization is `(card Y)^{1/2}` times the printed `‖·‖₂`, so the normalization costs nothing |

### The `thm:transport` chain

Seven modules, all PROBE GREEN and landed, all in their own sub-namespaces.

| commit | module | jobs | what it carries |
| --- | --- | --- | --- |
| `0e482802f` | `HilbertSchmidtAdMatrix.lean` | 3294 | the printed choice of matrix units (`adMatrix`) and `‖Ad(A) − Ad(B)‖ ≤ 2‖A − B‖` |
| `c27107027` | `HilbertSchmidtOperatorAction.lean` | 3295 | the action `applyOp M a`, `‖M x‖₂ ≤ ‖M‖‖x‖₂`, and the triangle inequality for `‖·‖₂` with no constant |
| `0fa6cad2e` | `TransportPrintedCommutant.lean` | 3330 | the printed `𝒞₂(V,L)` (Hilbert--Schmidt bounded) and `PrintedTransportHS` |
| `586410f4e` | `TransportSigmaTilde.lean` | 3296 | `σ̃(g) = [Ad(V_n(g))]_n ∈ U(𝓑)` |
| `3a12c7c53` | `TransportKazhdanProjection.lean` | 3315 | `exists_combination_close` at arbitrary `ε`, and `limsup_n ‖P_n − Σ a_ℓ Ad(V_n(ℓ))‖ < ε` |
| `a91fa6849` | `TransportProjectionCommutation.lean` | 3433 | `P`, `P_n`, and `[U, P] = 0` |
| `2cfea8185` | `TransportProjectionCharacterization.lean` | 3433 | `(x_n) ∈ 𝒞₂(V,L) ↔ ‖P_nx_n − x_n‖₂ → 0`, both directions |
| `cea8aa4fd` | `TransportPrintedRoute.lean` | 3434 | the closing estimate and the endpoint `manuscriptPrintedTransportHS : PrintedTransportHS` |

### Sentence to lemma table (`thm:transport`, current printed proof)

| printed sentence | carrier |
| --- | --- |
| "For unitaries `A, B`, `‖Ad(A) − Ad(B)‖ ≤ 2‖A − B‖`" | `HilbertSchmidtAdMatrix.norm_adMatrix_sub_le` |
| "The algebra `𝓑` is a norm matrix corona with coordinate sizes `d_n²` after a choice of matrix units" | `HilbertSchmidtAdMatrix.adMatrix` with `adMatrix_one`, `adMatrix_mul`, `adMatrix_conjTranspose`, `adMatrix_mem_unitary` |
| "the maps `Ad(V_n(g))` are asymptotically multiplicative in operator norm and `σ̃(g) = [Ad(V_n(g))]_n ∈ U(𝓑)` is a homomorphism" | `TransportSigmaTilde.tendsto_adMatrix_defect`, `TransportSigmaTilde.sigmaTilde` |
| "Let `P ∈ 𝓑` be the image of the Kazhdan projection … and lift `P` to orthogonal projections `P_n` … by functional calculus" | `TransportProjectionCommutation.exists_projectionData` |
| "by density of the group algebra … `‖Σ a_ℓ u_ℓ − e_L‖ < ε`; the trivial character gives `\|Σ a_ℓ − 1\| < ε`" | `TransportKazhdanProjection.exists_combination_close` |
| "`Σ a_ℓ σ̃(ℓ)` is within `ε` of `P`, so `limsup_n ‖P_n − Σ a_ℓ Ad(V_n(ℓ))‖ ≤ ε`" | `TransportKazhdanProjection.limsup_norm_sub_combSeq_lt` |
| "`(x_n) ∈ 𝒞₂(V,L)` … so `limsup_n ‖P_nx_n − x_n‖₂ ≤ 2εc`, and `ε` was arbitrary" | `TransportProjectionCharacterization.tendsto_hsNorm_applyOp_projection_sub` |
| "`u_ℓ e_L = e_L` … so `σ̃(ℓ)P = P` and `‖Ad(V_n(ℓ))P_n − P_n‖ → 0`" | `TransportProjectionCharacterization.tendsto_norm_adMatrix_mul_projection_sub` |
| "if `‖P_nx_n − x_n‖₂ → 0`, then `‖Ad(V_n(ℓ))x_n − x_n‖₂ ≤ 2‖x_n − P_nx_n‖₂ + ‖Ad(V_n(ℓ))P_n − P_n‖‖x_n‖₂ → 0`" | `TransportProjectionCharacterization.isHSAsymptoticallyCentral_of_tendsto` |
| "Put `U = σ̃(u)` … `U*PU ≤ P` … `U*PU = P` … So `[U, P] = 0`" | `TransportProjectionCommutation.commute_sigmaB_projection` |
| "`‖[Ad(V_n(u)), P_n]‖ → 0`" | `TransportPrintedRoute.tendsto_norm_commutator` |
| "`‖P_n Ad(V_n(u))^{±1}x_n − Ad(V_n(u))^{±1}x_n‖₂ ≤ … → 0`, so `Ad(V(u))^{±1}x ∈ 𝒞₂(V,L)`" | `TransportPrintedRoute.tendsto_hsNorm_applyOp_projection_sub_of` |
| the theorem | `TransportPrintedRoute.manuscriptPrintedTransportHS` |

### Three departures from the printed words, for the census

1. The printed definition of `𝒞₂` changed to the Hilbert--Schmidt bound.
   `PrintedTransportHS` is stated at the new definition; the old carrier
   `manuscriptOneSidedKazhdanTransportCommutantEquality` is about
   `boundedHSCommutant`, whose bound is the operator norm.  The old set is
   contained in the new one (`boundedHSCommutant_subset`), so the new
   statement is the stronger one, and the old module is untouched.
2. The order relation is taken in the conjugated form `P ≤ U P U*` rather
   than the printed `U*PU ≤ P`.  They are the same statement conjugated by
   `U`, and `conj_image_mul_image` states the first directly, so no order
   structure has to be installed on the corona.
3. The printed `‖·‖₂` is the normalized Hilbert--Schmidt norm.  The
   vectorization used to reach `EuclideanSpace` is isometric only up to the
   factor `(card Y)^{1/2}`; `HilbertSchmidtOperatorAction.norm_vecE` is that
   bookkeeping, and the factor cancels in every estimate.

## Not done, with the exact open obligations

All three printed proofs in scope now have printed-route carriers.  Nothing in
this lane's brief remains.

## Reopened lane, 2026-09-07: per-sentence carriers for four analytic blocks

`Manuscript/OneSidedMFRadical/CompressionCriterionSentences.lean`, sub-namespace
`CompressionCriterionSentences`.  Fourteen `manuscriptSentence_*` declarations,
one per printed sentence, each with the sentence quoted in its docstring and
each carrying `#audit_axioms`.  Every one is a wrapper over lemmas already on
`origin/main` except `conjugatedMap_opNormVanishing`, which is new.

### `thm:compression-criterion`, the introduction's outline paragraph

| census id | printed sentence | carrier | status |
| --- | --- | --- | --- |
| `5c4b238d20db` | "Asymptotic multiplicativity … makes the conjugation maps `Ad(V_n(g))` an asymptotically multiplicative family of unitaries on `M_{d_n}(ℂ)` with its normalized Hilbert--Schmidt inner product" | `manuscriptSentence_adIsAsymptoticallyMultiplicativeUnitaryFamily` | unconditional |
| `b529b81ba1b5` | "`‖Ad(A) − Ad(B)‖ ≤ 2‖A − B‖`" | `manuscriptSentence_adIsTwoLipschitz` | unconditional (both arguments unitary, the printed context) |
| `7cb15e1cfb7c` | "The classes of these maps form a homomorphism of `G` into the unitary group of the norm matrix corona with coordinate sizes `d_n^2`" | `manuscriptSentence_adClassesFormCoronaHomomorphism` | unconditional |
| `8c90718559ac` | "Let `U` be the class of `(Ad(V_n(u)))` and `P` the image of the Kazhdan projection of `L` in that corona" | `manuscriptSentence_compressorClassAndKazhdanProjectionImage` | unconditional (a naming sentence: both objects exist and `P` is a projection) |
| `3669402cc535` | "Property (T) of `K` turns this into triviality in operator norm" | `manuscriptSentence_propertyTUpgradesHSTrivialityToOperatorNorm` | unconditional (the closed `NormalKazhdanRadical`, proved by the printed route) |
| `77affad8cafd` | "A corona homomorphism nontrivial on `K` compresses to a corner where the Kazhdan projection of `K` vanishes" | `manuscriptSentence_nontrivialCoronaHomCompressesToKillingCorner` | unconditional |
| `72532c7673ac` | "On that corner, a group-algebra element within `1/4` … has operator norm below `1/4`, while Hilbert--Schmidt triviality sends its normalized traces to the sum of its coefficients, which exceeds `3/4`" | `manuscriptSentence_cornerNormBelowQuarterTraceAboveThreeQuarters` | unconditional, but a proof step: it consumes the printed corner data (`PrintedCornerData` and the class identity), as the sentence itself does |

### The "Kazhdan transport" setup paragraph

| census id | printed sentence | carrier | status |
| --- | --- | --- | --- |
| `fd2cafafd8fa` | "For an actual representation `ρ : G → U(d)` … the two spaces have the same finite dimension, so the inclusion is an equality; … and `ρ` is trivial on `𝔇_G(L)`" | `manuscriptSentence_exactRepresentationCommutantDimensionCount` | unconditional, and stated under a weaker hypothesis than printed |
| `b1b62a9e3c06` | "An asymptotic representation has no exact commutant to count" | `manuscriptSentence_asymptoticRepresentationHasNoExactCommutant` | **structural** |
| `240357aed76a` | "Property (T) supplies a Kazhdan projection in its place, and stable finiteness of the corona replaces the dimension count" | `manuscriptSentence_kazhdanProjectionAndStableFinitenessReplaceTheCount` | unconditional |

### `cor:defect-hs`, the printed proof

| census id | printed sentence | carrier | status |
| --- | --- | --- | --- |
| `310f6df94cdf` | "Since `c` commutes with `L`, `(V_n(c)) ∈ 𝒞₂`, so `(V_n(u)V_n(c)V_n(u)*) ∈ 𝒞₂` … and then `(V_n(ucu⁻¹)) ∈ 𝒞₂` because `‖…‖ → 0`" | `manuscriptSentence_conjugatedCentralizerStaysInPrintedCommutant` (new helper `conjugatedMap_opNormVanishing`) | unconditional |
| `a6988bc68f49` | "So `‖V_n(ℓ)V_n(ucu⁻¹) − V_n(ucu⁻¹)V_n(ℓ)‖₂ → 0`, and by asymptotic multiplicativity `‖V_n([ucu⁻¹, ℓ]) − 1‖₂ → 0`" | `manuscriptSentence_hsCommutatorVanishesAndDefectIsHSTrivial` | unconditional |
| `acc79ac4eb5f` | "The elements with this property form a normal subgroup of `G`, so it contains `𝔇_G(L)`" | `manuscriptSentence_hsTrivialElementsFormNormalSubgroupWithDefect` | unconditional |

### "From Hilbert--Schmidt to operator norm", the setup sentence

| census id | printed sentence | carrier | status |
| --- | --- | --- | --- |
| `c9d3bf1f96b3` | "Restricting a corona homomorphism `ρ` to a corner requires a correction: … the compressions `q_n U_n(g) q_n` are only approximately unitary in the matrix corners" | `manuscriptSentence_cornerCompressionsAreOnlyApproximatelyUnitary` | unconditional |

### The one new lemma, and why it had to be new

`conjugatedMap_opNormVanishing` is `‖V_n(u)V_n(c)V_n(u)* − V_n(ucu⁻¹)‖ → 0`.
Grepping `OpNormVanishing` over `origin/main` turns up the same shape only
inside `Sofic/KazhdanCompressorCorner.lean`, where `conj_defect_vanishing`
proves it against the *adjoint* almost representation, for a compressed
generator, and as one step of the rotated-corner argument.  Nothing states it
for a conjugated centralizer element of the ambient group, which is what the
printed "because `‖V_n(u)V_n(c)V_n(u)* − V_n(ucu⁻¹)‖ → 0`" needs.  It is three
vanishing pieces: the multiplicative defects of `u · c` and `(uc) · u⁻¹`, and
the inversion defect `V_n(u⁻¹) − V_n(u)*`, each multiplied by a contraction.

### Departures the census should know about

1. `b1b62a9e3c06` is a negative prose remark with no mathematical claim.  Its
   carrier is the unfolding of `boundedHSCommutant`, true by `rfl`, recording
   that the printed `C₂` is cut out by two limit conditions and by no exact
   commutation relation.  It is a **structural** carrier, not a theorem.
2. `fd2cafafd8fa` is carried by `manuscriptFiniteDimensionalCommutantRigidity`,
   which asks only for a finite-dimensional representation over a field, not
   for a unitary representation in `U(d)`.  That is a weaker hypothesis than
   printed, so the carrier proves more, not less.  The "same finite dimension,
   so the inclusion is an equality" clause is a map *equality*
   (`fixedSubmodule_map_eq`), not an inclusion.
3. `310f6df94cdf` is proved at `boundedHSCommutant`, the operator-norm-bounded
   asymptotic commutant, because that is where `thm:transport` is available as
   a set equality.  The printed `C₂` is now the larger Hilbert--Schmidt-bounded
   `printedCTwo`, so the carrier's fourth conjunct pushes all three memberships
   across `boundedHSCommutant_subset` and the sentence is matched at the
   printed definition too.
4. `77affad8cafd`'s carrier is stated for `B : Type` rather than `B : Type v`,
   because `manuscriptSentence_complementNonzero` is a `Type 0` statement.  The
   corona is `Type 0`, so nothing printed is lost.
5. The footnote of `72532c7673ac` (a Hilbert--Schmidt bound on the
   multiplicative defect does not give an operator-norm bound on the
   conjugation maps, so the argument does not apply to sofic or hyperlinear
   approximations) is `manuscriptFullRadicalsDoNotEntailNonsoficity` and is not
   restated here; the census already cites it on that row.

### Two sentences of the block that are not this lane's

The lead counted nine census sentences for `thm:compression-criterion`.  Seven
are the outline paragraph above.  The other two, `6b5d4b5c3081` (the pair
`ts = 1`, the explicit `u ∈ EL₄(R)` conjugating `EL₃(R)`, and one commutator
normally generating `EL₄(R)`) and `4489913ea11c` (the ring `𝒞` and
`B = EL₄(𝒞)` mapping onto every `EL_n(R)` with normally generating image), are
ring-theoretic and already have carriers in the ring lane's
`FullDefectRingSentences.lean` and `UniversalGroupB.lean`:
`manuscriptSentence_compressorMatrix`, `manuscriptSentence_intertwine`,
`manuscriptSentence_defectIsEverything` for the first, and
`manuscriptSentence_ringRelations`, `manuscriptSentence_imageOfB`,
`UniversalGroupB.exists_hom_normallyGenerating` for the second.  I have not
duplicated them.
