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

## Not done, with the exact open obligations

The tex owner has landed ultrafilter-free proofs of `thm:transport` and
`lem:central-corona-corner` as well, so both are in scope; neither is done.

### `lem:central-corona-corner` (`Manuscript/OneSidedMFRadical/CentralCoronaCorner.lean`)

The Lean carrier `manuscriptCentralCoronaCorner` proves the exact printed
statement, but by the *old* route: `CollapseNormalizedSetup.exists_projection_lift_and_ultrafilter`
(a free ultrafilter), a polar-decomposition unitary lift of `ρ(g)`, and
BDL Proposition 2.4 to correct the compressions `q_n U_n(g) q_n`.  The current
printed proof does none of that.  It instead

1. lifts `q` to projections `q_n` (available: `CollapseProjectionLift.exists_projection_lift`);
2. observes that `q ≠ 0` forces infinitely many `q_n ≠ 0` (easy from
   `normMatrixCStarCoronaMk_eq_zero_iff`; no ultrafilter);
3. identifies `q 𝒬_d q` with the corona `𝒬_r` over the corners, via
   `(z_n) ↦ (q_n z_n q_n)` in the corner coordinates;
4. notes that `g ↦ q ρ(g)` is a homomorphism into the unitary group of that
   corner, with unit `q`;
5. lifts each of its values to unitaries `W_n(g) ∈ U(r_n)` "as in the proof of
   `lem:stable-finite`" (available: `CollapseUnitaryLift.liftFam` /
   `CollapseUnitaryLift.coronaAlmostRep`, which already produces an
   `OpAlmostRepresentation` from a corona homomorphism);
6. reads off the corona class of `(J_n W_n(g) J_n*)`.

Step 3 is the whole gap and the only new mathematics.  The open obligation, as
a Lean statement, is a `⋆`-isomorphism onto the corner:

```lean
def cornerCoronaEquiv
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (Q : BoundedMatrixSequence (fun n ↦ X n))
    (hQ : ∀ n, IsOrthogonalProjectionMatrix (Q n))
    (hQne : ∀ n, (Q : ∀ n, Matrix (X n) (X n) ℂ) n ≠ 0) :
    NormMatrixCStarCorona (fun n ↦ X n) →⋆ₙₐ[ℂ]
      NormMatrixCStarCorona (fun n ↦ cornerModelOf (hQ n))
```
carrying `z ↦ [cornerCompression (hQ n) (z n)]`, together with

```lean
theorem norm_cornerCoronaEquiv_of_corner
    (z : NormMatrixCStarCorona (fun n ↦ X n)) :
    ‖cornerCoronaEquiv X Q hQ hQne (q * z * q)‖ = ‖q * z * q‖
```
(`q = [Q]`), which is the injectivity on the corner that makes the printed
"identify the corner with the corona" legitimate.  Steps 1, 2, 4, 5, 6 are then
short.  Everything else needed is already in `Analysis/CornerMatrixEmbedding`
(`cornerEmbed`, `norm_cornerEmbed`, `cornerEmbed_mul`,
`cornerEmbed_cornerCompression`) and `Analysis/CollapseUnitaryLift`.

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

Missing: the identification of `B(M_{d_n}(ℂ))` (Hilbert--Schmidt inner product)
with `M_{d_n²}(ℂ)` as a `FiniteModel`, i.e.

```lean
def hsMatrixUnitsEquiv (Y : FiniteModel) :
    (Matrix Y Y ℂ →L[ℂ] Matrix Y Y ℂ) ≃⋆ₐ[ℂ] Matrix (Y × Y) (Y × Y) ℂ
```
carrying the operator norm of the normalized Hilbert--Schmidt inner product to
the `L2Operator` norm of `Matrix (Y × Y) (Y × Y) ℂ`.  Without it the printed
`𝓑` is not a `NormMatrixCStarCorona` and none of the corona API applies.  The
density/trivial-character half of the printed proof is exactly the estimate
`manuscriptSentence_denseCombinationAndCharacter` and
`manuscriptSentence_limsupCombinationLtQuarter` already carry, so it should be
reusable once `𝓑` is a norm matrix corona.
