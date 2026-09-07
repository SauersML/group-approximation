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
