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

## Not done, with the exact open obligations

`thm:transport` is the only printed proof of the three still without a
printed-route carrier.

### `thm:transport` (`Manuscript/OneSidedMFRadical/TransportCommutantEquality.lean`)

The current printed proof runs entirely inside a second corona: it forms
`σ̃(g) = [Ad(V_n(g))]_n` in
`∏_n B(M_{d_n}(ℂ)) / ⊕_n B(M_{d_n}(ℂ))`, notes that this is a norm matrix
corona with coordinate sizes `d_n²` after a choice of matrix units, puts the
image `P` of the Kazhdan projection there, lifts `P` to projections `P_n` on
the Hilbert--Schmidt Hilbert spaces, and proves

> `(x_n) ∈ 𝒞₂(V,L)` if and only if `‖P_n x_n − x_n‖₂ → 0`

by the same density-plus-trivial-character estimate this lane already
formalizes for `thm:normal-kazhdan`.  The one-sided order and stable finiteness
then give `U*PU = P`, hence `[U,P] = 0`.

Missing: the identification of `B(M_{d_n}(ℂ))`, the operators on the
Hilbert--Schmidt Hilbert space, with `M_{d_n²}(ℂ)` as a `FiniteModel`, i.e. a
`⋆`-isomorphism

```lean
def hsMatrixUnitsEquiv (Y : FiniteModel) :
    (HS Y →L[ℂ] HS Y) ≃⋆ₐ[ℂ] Matrix (Y × Y) (Y × Y) ℂ
```
carrying the operator norm of the Hilbert--Schmidt inner product to the
`L2Operator` norm of `Matrix (Y × Y) (Y × Y) ℂ`.  Without it the printed `𝓑`
is not a `NormMatrixCStarCorona` and no corona API applies.

Two things make this smaller than it looks.

* **The normalization is free.**  The printed norm is
  `‖a‖₂ = tr_d(a*a)^{1/2}`, the *normalized* Hilbert--Schmidt norm, which is
  `d^{-1/2}` times the Frobenius norm.  Scaling an inner product by a positive
  constant changes neither the unitary group nor the operator norm on `B(·)`,
  so the identification may be built over the plain Frobenius inner product,
  for which Mathlib already has
  `Matrix.frobeniusSeminormedAddCommGroup` / `Matrix.frobeniusNormedSpace`
  (scoped, in `Mathlib/Analysis/Matrix/Normed.lean`).  Only the final estimates
  need the factor put back, and they are estimates about `‖·‖₂` of matrices,
  which the corpus already has as `hsNorm`.
* **The matrix-units step is Mathlib's.**  `Matrix Y Y ℂ` with the Frobenius
  inner product is `EuclideanSpace ℂ (Y × Y)` after uncurrying, and
  `Matrix.toEuclideanCLM` (`Mathlib/Analysis/InnerProductSpace/PiL2.lean`) is
  already a `⋆`-algebra equivalence `Matrix (Y × Y) (Y × Y) ℂ ≃⋆ₐ[ℂ]
  EuclideanSpace ℂ (Y × Y) →L[ℂ] EuclideanSpace ℂ (Y × Y)` that the
  `L2Operator` norm is *defined* through.  What has to be written is the
  linear isometry equivalence `Matrix Y Y ℂ (Frobenius) ≃ₗᵢ[ℂ]
  EuclideanSpace ℂ (Y × Y)` and the conjugation it induces on the bounded
  operators.

After that the printed proof needs, in order:

1. `‖Ad(A) − Ad(B)‖ ≤ 2‖A − B‖` on the Hilbert--Schmidt space, hence
   `σ̃(g) = [Ad(V_n(g))]` is a homomorphism into `U(𝓑)`;
2. the image `P` of the Kazhdan projection of `L` in `𝓑` and a projection lift
   `P_n` (`CollapseProjectionLift.exists_projection_lift`, as used above);
3. `(x_n) ∈ 𝒞₂(V,L) ↔ ‖P_n x_n − x_n‖₂ → 0`.  The forward direction is
   *exactly* the density-plus-trivial-character estimate this lane already
   carries: `NormalKazhdanPrintedRoute.exists_generatorCombination_close`
   plus `manuscriptSentence_denseCombinationAndCharacter` (with `1/4` replaced
   by an arbitrary `ε`), and the reverse direction is
   `MaximalCStarKazhdanProjection.generator_mul_projection` transported by
   `rep_mul_image`;
4. `U*PU ≤ P` from `manuscriptLiteralMaximalCStarKazhdanProjectionOrder`, and
   `U*PU = P` from `manuscriptNormMatrixCoronaStableFinite`, hence `[U,P] = 0`;
5. the closing two-line estimate.

Steps 2, 4 and most of 3 are already in the corpus; steps 1 and the
identification are the new work.
