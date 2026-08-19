# Step-for-step audit of the involutive collapse theorem

**Target.** `non_mf_groups_exist.tex`, `\subsection{Orbit collapse and defect
saturation}\label{subsec:collapse}` — Definition `def:invwitness`, Theorem
`thm:collapse` (*involutive collapse*) and its `\begin{proof}[Proof sketch]`
Steps 1–6, plus Remark `rem:collapse-finite-stage`.

**Standard applied.** Step-for-step identity *within* each stage: same
intermediate objects, same inferences, same order. A correct shortcut is a
mismatch. A stronger lemma bypassing an intermediate step is a mismatch. An
equivalent-but-different invariant is a mismatch. Matching six stage headings is
**not** the standard, and the earlier verdict that "Lean follows the same six
stages and merely fills in bookkeeping" is withdrawn below at five specific
places.

**Standard applied to the sketch.** The TeX prints a *sketch*. Where the sketch
genuinely under-determines a step, Lean cannot be charged with deviating; those
places are reported separately, in §5, as findings **about the manuscript**.

**Method.** Navigated by `\label{}` and quoted phrases. Every Lean judgement
below is from reading the proof body, not the statement. Nothing was compiled
(hard rule); no `.lean` or `.tex` file was touched.

> **Status re-check, 2026-08-16 (against `non_mf_groups_exist.tex` at 4526
> lines).** Findings **S2** and **S3** below are **closed by the current
> manuscript** and should not be re-raised; they are kept for the record. This
> note exists because the audit was read as current and its S2 was re-reported
> as a live gap in the printed proof.
>
> - **S3 closed.** Step 5 now opens "Fix a free ultrafilter $\omega$ on $\N$"
>   and works in the Hilbert-space ultraproduct $K_\omega$. It is an ultralimit,
>   not a `limsup`.
> - **S2 closed.** The Step 5 → Step 6 interface no longer runs through a
>   primitive at a prescribed tolerance, so the quantifier gap S2 describes
>   ($\forall\delta\,\exists y^\delta$ does not give one $y$ with $o(k_n)$
>   defect) has nothing to attach to. Step 5 gets an **exact** coboundary
>   $b(\gamma)=y-\pi(\gamma)y$ from Delorme–Guichardet applied to a genuine
>   1-cocycle in $K_\omega$ — the cocycle identity being licensed by Step 4's
>   *vanishing* defect mass at scale $k_n$, not by a fixed tolerance. Step 6
>   then transports the **fixed vector** $y$, and it does so with the projection
>   chain only: build $P$ onto $\operatorname{Fix}\pi(L)$ from the Kazhdan gap,
>   set $Q=VPV^{*}$, get $P\le Q$ from the range inclusion, get $P\sim Q$ from
>   $r=V^{*}Q$, conclude $Q=P$ by finiteness of the norm ultraproduct. That
>   chain is present in the proof of `thm:kazhdan-transport` (checked), and no
>   transported sequence enters it — the sequence $x_n$ appears only in that
>   proof's final "Conclusion" paragraph, which Step 6 does not use. So neither
>   of S2's two suggested repairs is needed; the printed proof takes a third
>   route that avoids the hypothesis.
> - The word "circumcenter" does not occur in the proof of `thm:collapse`; the
>   circumcenter argument is in the property-(T) verification for $\mathcal B$,
>   a different place. Confusing the two is the likely source of the re-report.
> - Also re-checked while here: the $\kappa\le1$ normalization behind the
>   $3/64$ estimate **is** stated ("Shrinking $\kappa$ costs nothing … so assume
>   $\kappa\le1$"), and its single use is flagged in situ ("the last inequality
>   is where $\kappa\le1$ is used"). The joint-corner correction in Step 1 is
>   stated, with the commutant identified as a finite intersection of joint
>   spectral corners.
>
> Findings S1, S4, S5 and the Lean-side findings are **not** re-checked here.

**Chain hygiene (checked).** `sorry` = 0, `axiom` = 0, `native_decide` = 0
across the whole collapse chain. Property (T) is consumed through the in-repo
Delorme theorem (`Kazhdan/DelormeFixedPoint.lean`,
`bounded_of_gaussian_isPositiveDefinite`, proved via GNS + Kazhdan spectral
gap), and (T) ⇒ finite generation through
`KazhdanFiniteGeneration.exists_symmetric_generating_finset`. No hypothesis in
the chain stands in for an unformalized theorem.

---

## 1. The declaration under audit

| TeX | Lean |
| --- | --- |
| `def:invwitness` (W1)(W2)(W3) | `InvolutionCollapseEndpoint.IsInvolutiveCompressionWitness` |
| `def:invwitness` `D_coll(L,s)` | `InvolutionCollapseEndpoint.involutiveCollapseDefect` |
| `thm:collapse` | `ManuscriptExactWrappers.manuscriptInvolutiveCollapse` → `InvolutionCollapseEndpoint.involutiveCollapseDefect_le_actualCoronaMFResidual` |
| sketch, all six steps | `InvolutionCollapseEndpoint.no_marked_model` (single proof, ~260 lines) |
| `Rad_MF` (`def:radical`) | `actualCoronaMFResidual` |

`ManuscriptExactWrappers.manuscriptInvolutiveCollapsePattern` discharges the
object identity of the witness predicate and of the defect by `Iff.rfl` / `rfl`
— i.e. `IsInvolutiveCompressionWitness` is *literally* the displayed
`k²=1 ∧ (∀γ∈L, Commute (sγs⁻¹) k) ∧ (∀γ₁,γ₂∈L, Commute (γ₁kγ₁⁻¹) (γ₂kγ₂⁻¹))`,
and `involutiveCollapseDefect` is *literally* the normal closure of
`{⁅γ,k⁆ : γ∈L, k a witness}`. Those two are unimprovable.

---

## 2. Verdict summary

| Verdict | Count | Steps |
| --- | --- | --- |
| EXACT | 30 | COL.01–.05, .07–.16, .18, .21–.27, .29–.32, .34, .36–.39 |
| MISMATCH | 9 | COL.06, .17, .19, .20, .28, .33, .35, .40 (scope), and the route-level finding R1 |
| MISSING | 0 | — |

No step of the printed argument is unformalized. Every mismatch is either an
object substitution that is *eventually equivalent*, or a route substitution
that proves the same conclusion by a different (quantitative) mechanism. None
of them is a hole; all of them are real deviations at the stricter standard.

---

## 3. Atomized steps

Notation: TeX symbols on the left; Lean declarations named in full on first use.
`B` denotes the `OpAlmostRepresentation`, `V n γ` the corrected involution
microstates, `S` the Kazhdan generating set.

### Preamble — "Coordinate unitary lifts … after passing to a subsequence"

**COL.01** *Coordinate unitary lifts (`lem:unitarycorona`) give an
operator-norm almost representation `(U_{g,n})` on blocks `M_{d_n}(ℂ)`.*
— **EXACT.** `OperatorMF.exists_markedOpAlmostRepresentation_of_normMatrixCorona_ne_one`
chooses lifts by `QuotientGroup.mk_surjective`, gets eventual multiplicativity
from `normMatrixCorona_lift_eventually_multiplicative` (kernel = null sequences,
exactly the proof of `lem:unitarycorona`), and packages them as an
`OpAlmostRepresentation`.

**COL.02** *After passing to a subsequence there is `η>0` with
`‖U_{[γ₀,k],n} − 1‖ ≥ η` for every `n`.* — **EXACT.** Same declaration:
`normMatrixCorona_lift_frequently_marked_separated` gives `δ>0` on a large set,
and the diagonal over an exhaustion `F n` of the countable group extracts a
subsequence on which separation holds at *every* index — literally
`MarkedOpAlmostRepresentation.marked_separated : ∀ n, separation ≤ ‖…‖`.
Consumed in `InvolutionCollapseEndpoint.coronaMFInvisible_commutator` by
`by_contra` + this extraction, matching "suppose, toward a contradiction, that
some corona representation does not kill `[γ₀,k]`".

### Step 1 — exact commuting involution microstates

**COL.03** *`v_γ = γkγ⁻¹`.* — **EXACT.**
`InvolutionOrbitMicrostates.orbitElement iota k γ = iota γ * k * (iota γ)⁻¹`;
`raw B iota k n γ = B.map n (orbitElement …)` is `U_{v_γ,n}`.

**COL.04** *By (W1), (W3), and asymptotic multiplicativity the images
asymptotically commute and square to 1.* — **EXACT.**
`raw_involution_vanishing` (uses `orbitElement_mul_self` from (W1)) and
`raw_commute_vanishing` (uses (W3) via `horb`). Both are exactly
"group identity + multiplicative defect".

**COL.05** *The spectral sign of the Hermitian part of a unitary `u` is an
exact self-adjoint involution at operator distance at most `‖u²−1‖` from `u`.*
— **EXACT**, and unusually literal.
`ExactInvolutionLifts.exactInvolutionCorrection u = signOfHermitian
(hermitianPart u)`;
`exactInvolutionCorrection_isExactInvolution`;
`norm_exactInvolutionCorrection_sub_le : ‖exactInvolutionCorrection u − u‖ ≤
‖u*u − 1‖`, proved by the ½ + ½ split (`norm_hermitianPart_sub_eq_half_sq_defect`
+ eigenvalue-wise rounding `abs_sign_sub_le_abs_sq_sub_one`). The manuscript's
constant is matched exactly, with no smallness hypothesis.

**COL.06** *"Block compression along the finite commutative corner structure of
the previously corrected microstates preserves exact commutation."*
— **MISMATCH (structural, minor).**
The TeX names one compression, along the *joint* corner structure of the whole
previously corrected commuting family (the 2^m joint spectral blocks). Lean
instead compresses along the **two-block cut of one previously corrected
involution at a time** (`involutionStep R v = cornerInvolutionCorrection
(involutionCut R) v`, `involutionCut` being the Bool-indexed pair of affine
cuts), iterated over the family in
`exists_isExactInvolution_comm_of_isExactInvolution`. Preservation of the
commutations already achieved is then **not** a property of the compression
itself but a separate lemma, `involutionStep_commutant` ("the step never leaves
the commutant"), which has no counterpart in the TeX. Consequences:
* the joint-corner lemma the TeX describes *does* exist in the file
  (`cornerCompression`, `norm_cornerInvolutionCorrection_sub_le`, cost linear in
  the number of blocks) but is used only as the two-block instance;
* the accumulated cost is `3·15^{|window|}·ε`, exponential in the window,
  where the TeX's phrasing suggests the linear-in-blocks bound. The exponential
  is harmless (tolerances are chosen after the window), but it is a different
  estimate.

**COL.07** *Induction over an enumeration of `L` yields exact pairwise-commuting
self-adjoint involutions `V_n(γ)` with `‖V_n(γ) − U_{v_γ,n}‖ → 0`.*
— **EXACT.** `InvolutionOrbitMicrostates.exists_family_on` (Finset induction
over a window, tolerance `ε₀` chosen from the window size) +
`exists_involutionMicrostates` (surjection `ℕ ↠ Γ`, windows `range(N+1)`,
tolerance `1/(N+1)`, `Nat.findGreatest` diagonal, `V = 1` off the window).
Output clauses are exactly `IsExactInvolution (V n γ)`, global pairwise
commutation, and `OpNormVanishing (V n γ − raw n γ)`.

**COL.08** *`‖U_{g,n}V_n(γ)U_{g,n}* − V_n(gγ)‖ → 0` for each fixed `g ∈ L`.*
— **EXACT**, but *derived* rather than produced by Step 1:
`InvolutionCollapseMetric.V_covariance_vanishing`, from `raw_covariance_vanishing`
(`orbitElement_conj`) plus the Step-1 convergence. Same object, same content;
the only difference is that the TeX packages it inside the Step-1 output.
One indexing note: TeX says "where `gγ` denotes the orbit index of `g v_γ g⁻¹`";
Lean indexes the family by `Γ` itself, not by the orbit set, so `V n` is a
`Γ`-indexed family and the displacement pseudometric lives on `Γ`. That is a
refinement (it is what the argument uses), not a weakening.

### Step 2 — the rank displacement metric

**COL.09** *`T = u − w` self-adjoint with `T³ = 4T`.* — **EXACT.**
`InvolutionRankMass.conjTranspose_sub_eq`, `sub_mul_sub_mul_sub`
(`(u−w)*((u−w)*(u−w)) = 4•(u−w)`), via `sub_mul_sub_of_commute` and
`sub_mul_mul_eq_neg_sub`. Commutation is used exactly where the TeX says it is.

**COL.10** *`T²/4` is an orthogonal projection.* — **EXACT.**
`halfSqProjection u w = (4:ℂ)⁻¹ • ((u−w)*(u−w))`,
`halfSqProjection_isOrthogonalProjection`.

**COL.11** *`Tr|u−w|² = 4·rank((u−w)²/4)`.* — **EXACT**, as an identity, not an
estimate: `matMass_sub_eq_four_mul_rank`, through
`matMass_eq_re_trace_conjTranspose_mul` and
`re_trace_eq_rank_of_isOrthogonalProjection`.

**COL.12** *`d_n(γ,μ) = rank(V_n(γ) − V_n(μ))` is an integer-valued
pseudometric.* — **EXACT.** `InvolutionCollapseMetric.dV`, `dV_triangle`
(= `rank_sub_le_add`, proved by `LinearMap.range_add_le` + `finrank_mono`),
`dV_symm`.

**COL.13** *Projections at operator distance below 1 have equal rank.*
— **EXACT.** `rank_eq_of_projections_close`, via injectivity of the compression
(`rank_le_of_norm_sub_lt_one`).

**COL.14** *Eventual translation invariance `d_n(gγ,gμ) = d_n(γ,μ)`.*
— **EXACT.** `eventual_invariance`: transports covariance error into
half-square-projection distance and applies COL.13 with `rank_unitary_conj`.
Same inference, same order, same triple-by-triple quantifier ("for all large
`n`, for each fixed triple").

### Step 3 — generator normalization

**COL.15** *(T) makes `L` finitely generated; fix a Kazhdan pair `(S,κ)`, `S`
finite symmetric.* — **EXACT.**
`KazhdanProjection.HasKazhdanPropertyT.exists_symmetric_generating_pair`
yields `1∈S`, symmetry, `closure S = ⊤`, `0<κ≤1`, `IsKazhdanPair`. Finite
generation is in-repo, not assumed.

**COL.16** *`k_n = Σ_{a∈S} d_n(1,a)`.* — **EXACT.**
`InvolutionCollapseMetric.kNorm B V S n = ∑ a ∈ S, dV B V n a 1` (a **sum**, as
printed — note that `Sofic/MaxDisplacement.lean`, the max-normalized variant of
the multi-mover dossier, is *not* on this path and normalizes differently).

**COL.17** *`d_n(1,γ) ≤ |γ|_S · k_n` eventually, for the word length `|·|_S`.*
— **MISMATCH (object).** Lean's
`InvolutionCollapseProfile.wordLen S hgen hsymm γ` is the length of a
**`Classical.choose`n word** for `γ`, not the word metric `|γ|_S = min`. The
inequality proved (`eventually_dV_le_wordLen_mul_kNorm`, by list induction using
COL.14 and COL.12 exactly as the TeX says) is therefore against an arbitrary
word length `≥ |γ|_S`. It is used consistently downstream (COL.20, COL.24), so
nothing breaks, but the manuscript's invariant `|·|_S` is not the Lean object.
Fixing this means defining the `S`-word metric and proving the same induction
for the minimal word — mechanical, but not currently done.

**COL.18** *If `k_n = 0` along a subsequence the whole orbit collapses to a
single exact involution and `‖U_{[γ₀,k],n} − 1‖ → 0`, against the separation;
so `k_n ≥ 1` for all large `n`.* — **EXACT** (contrapositive orientation).
`eventually_one_le_kNorm_of_marked` first shows `V n γ₀ ≠ V n 1` (from
`⁅ιγ₀,k⁆ = v_{γ₀}·v_1`, `hz`, plus the multiplicative defect and the Step-1
convergence — this *is* the TeX's "`‖U_{[γ₀,k],n} − 1‖ → 0`" computation), hence
`dV n γ₀ 1 ≥ 1`, then contradicts `k_n = 0` through the word bound. Same
ingredients, same order, run backwards.

### Step 4 — the displacement almost-cocycle

**COL.19** *`b_n(γ) = k_n^{-1/2}(V_n(γ) − V_n(1))`.* — **MISMATCH (object).**
`InvolutionCollapseProfile.bVec` is the **guarded** vector
```
if 0 < kNorm ∧ dV n γ 1 ≤ wordLen γ * kNorm then (√kNorm)⁻¹ • flatE (V n γ − V n 1) else 0
```
i.e. the manuscript's `b_n(γ)` capped to `0` at the stages where the word bound
of COL.17 has not yet kicked in. For each fixed `γ` the two agree eventually
(COL.17 + COL.18), and every downstream use is at the ultralimit, so the
difference is invisible — but the Lean object is not the printed one, and the
cap is what buys COL.20 *at every stage*.

**COL.20** *`‖b_n(γ)‖²_F ≤ 4|γ|_S` at every large stage.* — **MISMATCH
(strengthened, and against the substituted invariant).**
`norm_bVec_sq_le` proves `≤ 4·wordLen γ` at **every** stage, not eventually,
because of the COL.19 guard. Strengthening an intermediate estimate to remove
the "eventually" is a deviation from the printed step even though it is
harmless. Inherits COL.17's `wordLen`-vs-`|·|_S` substitution.

**COL.21** *`Σ_{a∈S}‖b_n(a)‖²_F = 4` whenever `k_n ≥ 1` (eq. `generator-mass`).*
— **EXACT.** `sum_normSq_bVec_eq_four`, an exact identity at every stage with
`0 < kNorm`, via `matMass_V_sub` (= COL.11) and `Σ_S dV a 1 = kNorm`.

**COL.22** *Conjugation by `U_{a,n}` is a Frobenius isometry.* — **EXACT.**
`InvolutionCollapseCocycle.adFlat` + `norm_adFlat`.

**COL.23** *`D_n = (V_n(γ)−V_n(1)) − U_a(V_n(μ)−V_n(1))U_a* − (V_n(a)−V_n(1))`,
`μ = a⁻¹γ`.* — **EXACT.** The matrix `M` inside
`eventually_coboundary_defect_small` is character-for-character this expression,
and `hdefect` identifies `k_n^{-1/2}·M` with the cocycle defect of `bVec`.

**COL.24** *Grouping I: `rank D_n ≤ d_n(γ,1)+d_n(μ,1)+d_n(a,1) ≤
(|γ|+|μ|+|a|)k_n`.* — **EXACT.** `hrankN` (two applications of `rank_add_le`,
`rank_neg`, `rank_unitary_conj`) then `hrank` via COL.17.

**COL.25** *Grouping II: `D_n =(V_n(γ)−U_aV_n(μ)U_a*) + (U_aV_n(1)U_a*−V_n(a))`,
so `‖D_n‖ → 0`.* — **EXACT.** `hMsplit` is literally the regrouping; `hcov₁`,
`hcov₂` are the two Step-1 covariance errors (COL.08); `hMop : ‖M‖ ≤ 2η`.

**COL.26** *`Tr|D|² ≤ rank(D)·‖D‖²` bounds the normalized defect mass by
`(|γ|+|μ|+|a|)‖D_n‖² → 0`.* — **EXACT.**
`InvolutionRankMass.matMass_le_rank_mul_sq_opNorm` (proved by summing Gram
eigenvalues) applied in `hmass`, then divided by `k_n` in `hnormsq`. The
manuscript's remark that the norm bound alone cannot give the rank bound is
reproduced verbatim in the Lean docstring and is genuinely how the proof is
organized.

### Step 5 — bounded profile and an approximate primitive

**COL.27** *The Gaussians `e^{-t‖·‖²}` of the almost-cocycle are almost
invariant under the twisted action.* — **EXACT (mechanism).**
`UltralimitGaussian.isPositiveDefinite_exp_neg_mul_profile` derives positive
definiteness of `exp(−t·profile)` from the displacement identity
`profile(g⁻¹h) = lim‖b_n(h) − b_n(g)‖²`
(`InvolutionCollapseCocycle.profile_halmost`, itself proved from COL.23–COL.26).
The manuscript's "almost invariant" is the loose phrasing of this
positive-definiteness input; the Gaussian-kernel mechanism is the same.

**COL.28** *The spectral gap of `(S,κ)` bounds the limiting profile
`γ ↦ limsup_n‖b_n(γ)‖²_F` **by its generator values** (eq. `generator-mass`) —
Delorme's argument at the level of limiting seminorms.*
— **MISMATCH, on two counts.**
1. **Object.** The Lean limiting profile is `Ultralimit.seqNormSq =
   stdPart (ofSeq ‖·‖²)`, an **ultralimit along the hyperfilter**, not the
   `limsup` the manuscript prints. These are different functionals
   (ultralimit ≤ limsup in general). The ultralimit is in fact the *correct*
   object here — see finding S5 in §5 — so the manuscript, not Lean, is the
   party to move.
2. **Strength.** `UltralimitGaussian.profile_bounded_of_isKazhdanPair` returns
   only `∃ R, ∀ g, profile g ≤ R`, and the endpoint consumes it as an opaque
   `R₀` (then `Cw := √R + 2`). The manuscript's link *to the generator values*
   is not threaded: the limit-level anchor
   `InvolutionCollapseCocycle.sum_seqNormSq_bVec_eq_four` ("the generators carry
   total limiting mass exactly four") **is proved and then never used anywhere
   in the repository**. The quantitative content is present one level down —
   `Delorme.bounded_of_gaussian_isPositiveDefinite` internally produces
   `R = log 2 · 32 · (Σ_{q∈S} ψ q + 1)/κ²` — but that witness is discarded by
   the existential, so the printed "by its generator values" is not a Lean
   theorem about this profile.

**COL.29** *A circumcenter of the displacement orbit, taken at the level of
bounded sequences, produces one bounded `(w_n)` with
`b_n(a) ≈ w_n − U_a w_n U_a*` in limiting normalized mass, simultaneously for
any prescribed finite set of movers.* — **EXACT**, and this is the closest match
in the whole proof. `InvolutionCollapseCenter.exists_approximate_coboundary`:
orbit `O γ = bVec · γ`, radius `Ultralimit.orbitRadius`, optimal radius
`centerRadius`, near-optimal center `exists_near_center`, affine translate
`w' = adFlat(U_a)v + b(a)`, "the translate still nearly covers the orbit"
(using COL.23–COL.26 to show the defect sequence has zero seminorm), and the
approximate-circumcenter estimate `seqNormSq_sub_le_of_near_center` (a genuine
parallelogram-law argument). "Simultaneously for any prescribed finite set of
movers" is the explicit `T : Finset Γ` parameter. This is exactly the variant
licensed by `rem:collapse-finite-stage` ("the circumcenter by an approximate
circumcenter of a near-optimal covering sequence"). Note the primitive is
produced only at a **prescribed tolerance `δ`**, chosen in advance — see R1.

### Step 6 — transport through the compressor

**COL.30** *By (W2) the displacement vanishes on compressed elements.*
— **EXACT** as a Lean theorem, but the manuscript is silent on *why* — see S3.
`InvolutionCollapseEndpoint.hfixda` derives `orbitElement iota kk (δ_a) = kk`
from (W2), and `InvolutionCollapseEndpointPrep.eventually_bVec_eq_zero_of_orbit_fixed`
turns that into **exact** vanishing `bVec n δ_a = 0` for large `n`, using the
rigidity `InvolutionMicrostateTools.eq_of_norm_sub_lt_two` (commuting exact
involutions at operator distance `< 2` are equal).

**COL.31** *Including the compressed generators `sas⁻¹` among the movers makes
the primitive almost fixed by them.* — **EXACT.** `T := S ∪ S.image da` is the
mover set handed to COL.29; `compressed_primitive_limit` converts the
coboundary bound at `δ_a` into `seqNormSq (w − adFlat U_{ιδ_a} w) ≤ d₀`.

**COL.32** *Hence `u_n = U_s* w_n U_s` is almost fixed by every `a ∈ S`, because
microstates of `as⁻¹` and `s⁻¹(sas⁻¹)` agree asymptotically.* — **EXACT.**
`InvolutionCollapseEndpointPrep.mixed_conj_defect_vanishing` is exactly
"microstates of `ι(a)s⁻¹` and `s⁻¹ι(δ_a)` agree asymptotically"; combined with
COL.31 in `stage_conj_displacement`, which bounds the per-generator displacement
of `Xu = Usᴴ W Us` by `2τ`. The object `u_n = U_s* w_n U_s` is the manuscript's,
literally.

**COL.33** *Compression to the almost-fixed spectral subspace of the averaged
adjoint action of `S`.* — **MISMATCH (route: cited theorem bypassed; mechanism
matches).** Lean uses `KazhdanCompressorCorner.cornerProjection` = spectral
projection above `θ` of `hermitianAverage (gammaAdjoint B C) S n`, i.e. exactly
the almost-fixed spectral subspace of the averaged adjoint action, at
`θ` chosen just above `1 − κ²/(4|S|)`. The capture of `Xu` by that corner is
`InvolutionCollapseIndexCapture.index_capture` + `sqrt_residual_mass_le`,
assembled in `stage_capture`. The *mechanism* is the manuscript's. What is
bypassed is the manuscript's instruction to transport **"as in
Theorem `thm:kazhdan-transport`"**: see R1.

**COL.34** *Then the one-sided estimate `P ≤ VPV*` at the rescaled mass.*
— **EXACT.** `KazhdanCompressorCorner.one_sub_moved_mul_corner_vanishing` is
`‖(1−Q)P‖ → 0` with `Q = VPV*` — literally `P ≤ VPV*` in approximate form,
proved by the operator capture lemma on the rotated corner. Its companion
`one_sub_corner_mul_moved_vanishing` supplies the reverse `‖(1−P)Q‖` via
`norm_one_sub_mul_flip` + `movedProjection_rank` — the finite-stage
**equal-rank reversal** that `rem:finite-stage` says replaces finiteness of
`B_ω`. Both directions are present, in the manuscript's order.

**COL.35** *"Transporting forward … returns `w_n` up to vanishing mass, again
almost fixed by every `a ∈ S`."* — **MISMATCH (quantitative substitute for a
limit statement).** `stage_transport_bound` gives, at the single stage `n₀`,
`matMass(W − U_a W U_aᴴ) ≤ 18q²Cw² + 16κ`, via
`MarkedCompressionVectorChain.transported_displacement_le`. This is not
"vanishing mass": it is a fixed explicit bound, made smaller than `(ρt/2)²` by
`numeric_transport_bound` because `τ, q` were chosen in advance from `ρt`. Under
`rem:collapse-finite-stage` this substitution is licensed in spirit; it is still
not the printed inference.

**COL.36** *Then `b_n(a) ≈ w_n − U_a w_n U_a*` has small mass for every `a ∈ S`
at a common large stage, contradicting eq. `generator-mass`.* — **EXACT.**
`stage_generator_bound` gives `‖bVec n₀ a‖ ≤ ρt` for all `a ∈ S`;
`anchor_contradiction` closes against COL.21 with `ρt = 1/(√|S|+1)`, since
`|S|ρt² < 4`. The "common large stage" is the `.exists` of seven
hyperfilter-eventual facts (`hE1 … hE7`) — exactly
`rem:collapse-finite-stage`'s "the final contradiction assembled at one
sufficiently late coordinate".

**COL.37** *Normality of corona kernels extends the conclusion from the
commutators to all of `D_coll(L,s)`.* — **EXACT.**
`involutiveCollapseDefect_le_actualCoronaMFResidual` = `Subgroup.normalClosure_le_normal`
applied to `actualCoronaMFInvisible_of_involutiveWitness`.

### Statement-level

**COL.38** Witness predicate object identity — **EXACT** (`Iff.rfl`).
**COL.39** `D_coll(L,s)` object identity and normality — **EXACT** (`rfl` +
`Subgroup.normalClosure_normal`).
**COL.40** *"Let `H` be countable, `L ≤ H` with (T), `s` with `sγs⁻¹ ∈ L`; then
`D_coll(L,s) ≤ Rad_MF(H)`."* — **MISMATCH (scope).** The Lean theorem is fixed
at universe 0: `{H : Type} [Group H] [Countable H]`, `HasKazhdanPropertyT.{0,0}`.
The manuscript quantifies over all countable groups. Every countable group is
isomorphic to one in `Type 0`, so nothing mathematical is lost, but the
neighbouring wrappers (`manuscriptRadicalReductionToQuotient`) are stated at
`Type u`, so the restriction is a formalization artifact rather than a
convention. `Rad_MF` itself matches `def:radical` exactly
(`actualCoronaMFResidual` = intersection of kernels of all norm-matrix
C*-corona representations over all model sequences).

---

## 4. R1 — the compressor-transport stage and the rank weight

This is the item the audit was asked to check with particular care. The finding
is precise, and it is **not** the failure mode that was feared.

**What the manuscript asserts.** Two separate places:
* Step 6: "Transporting forward as in Theorem `thm:kazhdan-transport` —
  compression to the almost-fixed spectral subspace of the averaged adjoint
  action of `S`, then the one-sided estimate `P ≤ VPV*` at the rescaled mass —
  returns `w_n` up to vanishing mass".
* The discussion after `thm:transport-variants`: "the collapse proof of
  Theorem `thm:collapse` uses a rank weight, which normalizes a defect at its
  own scale." I.e. Step 6 is claimed to be an instance of
  `thm:transport-variants`(1) at weight `w_n = k_n`.

**What Lean does.**
1. **The rank weight is genuinely present, and the unweighted theorem is *not*
   substituted.** There is no dimension normalization anywhere in the collapse
   chain: every mass is `ScaledKazhdanTransport.matMass` (unnormalized
   `Σ|x_ij|²`) or `MarkedCompressionVectorChain.vecMass`, never divided by `d_n`.
   The `k_n` scale enters once, inside `bVec` (`(√kNorm)⁻¹ •`), so the primitive
   `w`, the matrix `W = unflatE (w n₀)`, and every estimate about them already
   live at the rank scale. Normalizing the objects up front and then using
   unweighted mass is mathematically the same as carrying the weight `w_n = k_n`
   through the transport. **The feared substitution of the plain
   dimension-normalized transport has not occurred.**
2. **But the cited theorems are never invoked.** Grepping the whole collapse
   chain: neither `KazhdanAsymptoticCommutant.manuscriptKazhdanTransport`
   (= `thm:kazhdan-transport`) nor
   `ScaledKazhdanTransport.scaled_transport_both`
   (= `thm:transport-variants`(1), already formalized and badged in the TeX)
   appears. The only `KazhdanAsymptoticCommutant` reference in
   `InvolutionCollapseEndpoint.lean` is the bookkeeping lemma
   `adjointMatrixSequence_mulVec_gammaRowVec`. Step 6 is re-derived inline as a
   one-stage chain: `stage_capture` → `stage_transport_bound` →
   `MarkedCompressionVectorChain.transported_displacement_le`. The two proofs do
   share the *same* corner machinery (`cornerProjection`, `movedProjection`,
   `one_sub_corner_mul_moved_vanishing`), so this is duplication of route, not
   divergence of mathematics — but at the stricter standard it is a route
   mismatch: the manuscript deduces Step 6 from a previously proved theorem, and
   Lean does not.
3. **Why the bypass is not gratuitous.** `scaled_transport_both` concludes
   `IsScaledAsymptoticCommutant`, defined through `ScaledMassVanishing`:
   `∀ ε > 0, eventually matMass(x_n − U x_n U*) ≤ ε·w_n`. The circumcenter of
   COL.29 does **not** produce a primitive with vanishing defect: it produces,
   for one tolerance `δ` fixed in advance, a primitive whose defect seminorm is
   `≤ δ`. So the qualitative theorem's hypothesis is unavailable, and the
   collapse needs a quantitative `ε ↦ f(ε)` transport at a single stage. That
   gap is a **manuscript** gap as much as a Lean one — see S4.

**What the collapse proof needs from the weighted transport** (spec for the
agent formalizing it):

* Data: `Γ = ↥L` with (T), `ι = L.subtype`, `s` the compressor,
  `U_n = B.map n` an `OpAlmostRepresentation` of the ambient group, weight
  `w_n = k_n = Σ_{a∈S} rank(V_n(a) − V_n(1)) : ℕ`. The statement must tolerate
  `w_n = 0` at finitely many stages (`k_n ≥ 1` only holds eventually), i.e. the
  `w_n = 0 ⇒ x_n = 0` convention of `thm:transport-variants`(1) is the right one.
* Input sequence: `x_n = √k_n · unflatE(w_n)` conjugated back by the compressor,
  `u_n = U_n(s)* x_n U_n(s)`.
  * mass bound `Tr(u_n* u_n) ≤ C·k_n` with `C = Cw²`, `Cw = √R + 2`, `R` the
    Delorme profile bound of COL.28;
  * displacement `Tr|u_n − U_n(ι a) u_n U_n(ι a)*|² ≤ ε·k_n` for `a ∈ S`.
* Required conclusion, **forward** direction only
  (`y_n = U_n(s) u_n U_n(s)* = x_n`):
  `Tr|y_n − U_n(ι a) y_n U_n(ι a)*|² ≤ f(ε)·k_n` for all `a ∈ S`.
* **Crucially, one of the following two must hold, and neither exists today:**
  * (a) a **quantitative** form with an explicit `f`, `f(ε) → 0`, depending only
    on `κ, |S|, C` and holding at a single stage where the corner estimates hold
    — this is what `stage_transport_bound` provides inline and what the printed
    Step 6 really needs; **or**
  * (b) the qualitative `∀ε` form (`scaled_transport_both`) **plus** a
    diagonalization lemma turning the family of `δ_j`-approximate primitives
    (`exists_approximate_coboundary` at `δ_j → 0`) into a *single* bounded
    sequence `w` with **vanishing** normalized coboundary defect on
    `S ∪ sSs⁻¹`. With that lemma, `scaled_transport_both` at weight `k_n` closes
    Step 6 directly and the Lean proof would match the printed route.
  Route (b) is the manuscript's literal reading and would be the cleanest
  1:1 repair; it costs one diagonalization lemma over `Ultralimit.seqNormSq`.

---

## 5. Findings about the manuscript (sketch silences)

These are places where the printed sketch under-determines the step, so no Lean
deviation can be charged — but the manuscript would need to be more explicit
before "1:1" is even a well-posed question. Listed in decreasing severity.

**S1 (severe). Step 6's "the displacement vanishes on compressed elements" is a
non sequitur as printed.** The displacement is a **rank**, and (W2) only gives
that the *raw* microstates of `s a s⁻¹` and of `1` converge to the same unitary
— an operator-norm statement. The manuscript itself insists two paragraphs
earlier (Step 4) that "two exact involutions at small operator distance can
differ in full rank". The step is nevertheless correct, because commuting exact
involutions at operator distance `< 2` are *equal*
(`InvolutionMicrostateTools.two_le_norm_sub_of_ne` /
`eq_of_norm_sub_lt_two`, from `T² = 4·halfSqProjection`). The manuscript never
states this rigidity. It should: without it Step 6's first sentence contradicts
Step 4's warning.

**S2 (severe) — CLOSED 2026-08-16, see the status note at the top of this file.
The current Step 5 gets an exact coboundary in the ultraproduct and Step 6
transports a fixed vector by the projection argument, so the interface below no
longer exists. Kept for the record.**
**The Step 5 → Step 6 interface is unspecified.** The circumcenter
delivers a primitive at a *prescribed* tolerance, not one with vanishing defect;
`thm:kazhdan-transport` and `thm:transport-variants`(1) both require the
displacement to tend to zero. The manuscript never says which of the two
repairs it intends (a quantitative transport, or a diagonalization over
tolerances). `rem:collapse-finite-stage` gestures at the first ("the limits in
the sketch above can be replaced by explicit tolerances") but does not connect
it to the transport theorem being cited. This is the single place where the
printed Step 6 cannot be executed as written.

**S3 (moderate) — CLOSED 2026-08-16: Step 5 now fixes a free ultrafilter and
works in the Hilbert-space ultraproduct. Kept for the record.**
**"limsup" should be an ultralimit.** Step 5 defines the limiting
profile as `γ ↦ limsup_n ‖b_n(γ)‖²_F`. Delorme's argument needs the profile to
satisfy the displacement identity `ψ(g⁻¹h) = ψ'(‖b(h) − b(g)‖²)` as an
*identity*, so that the Gaussians are positive definite; `limsup` is not a
limit functional and does not respect the required additivity. The Lean uses
`stdPart` along the hyperfilter — a genuine ultralimit — and the argument goes
through. The manuscript should say "limit along a fixed ultrafilter" (or
"ultralimit"), not "limsup".

**S4 (moderate). Step 1 never states the commutant-preservation property that
makes the induction work.** "Block compression … preserves exact commutation"
asserts that the *new* involution commutes with the corner. What the induction
actually needs is that the correction **stays inside the commutant**, so that
commutations achieved at *earlier* steps survive later corrections
(`involutionStep_commutant`). As printed, the induction hypothesis is not
obviously maintained. The manuscript should state the commutant property, or
say that the compression is taken along the *joint* corner of the whole
previously corrected family at once (in which case the single-shot estimate
`norm_cornerInvolutionCorrection_sub_le`, linear in the number of blocks,
applies and no commutant lemma is needed).

**S5 (moderate). Step 5's "bounds the limiting profile by its generator values"
is never used quantitatively, and it is not clear it is meant to be.** The
argument needs only *some* bound (the constant enters `Cw`, then `τ`, `q`). If
the manuscript intends the explicit generator-value bound (which Delorme does
give: `R = 32 log 2 · (Σ_S ψ + 1)/κ²`), it should say so and use it; otherwise
the phrase invites a reader to look for a quantitative dependence that plays no
role. As it stands the Lean's existential `R` is faithful to the *use* but not
to the *phrase*.

**S6 (minor). Step 2's rank-rigidity threshold is stated at the wrong level.**
"Projections at operator distance below 1 have equal rank" is applied to the
`V_n`, but the covariance error must first be pushed through the quadratic
`T ↦ T²/4`, which costs a factor (Lean needs covariance `≤ 1/8` per element,
`‖T‖, ‖T'‖ ≤ 2`, hence half-square distance `≤ 1/4 < 1`). The sketch omits the
quadratic step entirely.

**S7 (minor). Step 3's word bound needs the eventual sets to be chosen per
element.** `d_n(1,γ) ≤ |γ|_S k_n` "eventually" holds with a threshold depending
on `γ` (and on the chosen word); the sketch's "eventually" is unquantified, and
COL.17's list induction makes the dependence explicit.

**S8 (minor). Step 1's covariance is listed as an output of Step 1 but is a
consequence of its first clause.** Harmless, but it means Step 1 as printed
asserts two things where only one is constructed.

---

## 6. Withdrawal of the earlier verdict

The earlier audit's conclusion — "Lean follows the same six conceptual stages
and merely fills in bookkeeping; do not alter this section" — is too generous at
exactly five places, all documented above:

1. **R1 / COL.33, COL.35.** Step 6 cites a theorem (`thm:kazhdan-transport`,
   and at rank weight `thm:transport-variants`(1)) that the Lean proof never
   invokes, even though *both* are formalized and badged elsewhere in the
   manuscript. That is a route substitution, not bookkeeping — and the reason
   for it (S2) is a genuine gap in the printed argument.
2. **COL.30 / S1.** Lean supplies a rigidity lemma that carries an inference the
   TeX asserts flatly and that the TeX's own Step 4 appears to forbid.
3. **COL.06 / S4.** Lean's Step-1 induction rests on a commutant-preservation
   lemma with no counterpart in the manuscript, and compresses along a different
   corner structure with a different (exponential) cost.
4. **COL.17, COL.19, COL.20.** Two of the argument's central objects are
   substituted: `|γ|_S` becomes an arbitrary chosen word length, and `b_n(γ)`
   becomes a guarded vector that is zero at the pre-threshold stages.
5. **COL.28 / S3, S5.** The limiting profile is a different functional
   (ultralimit vs `limsup`), and the bound "by its generator values" is not
   established for it — the theorem that would establish it
   (`sum_seqNormSq_bVec_eq_four`) is proved and left unused.

None of these is a hole, and none of them makes `thm:collapse` doubtful: the
Lean chain is `sorry`-free, unconditional, and proves the printed conclusion
about the printed objects. The recommendation to leave the section untouched is
what should be reconsidered: S1–S3 in particular are places where the
*manuscript* is not yet a specification a formalization can be checked against.

---

## 7. Scope notes

* `thm:projection-collapse` (`ProjectionCompressionCollapse.corona_projection_collapse`),
  `thm:torsion-collapse`, `thm:commutinglamp`, `cor:collapsequot` and
  `thm:saturation` all sit in `subsec:collapse` and all *consume*
  `thm:collapse`; they were not atomized here.
* Modules named in the audit brief that turned out **not** to be on the
  `thm:collapse` path: `Sofic/MaxDisplacement.lean` and
  `Sofic/MoverGeneration.lean` (multi-mover dossier §5 / Cor. 4.2 — a max-based
  normalization, whereas COL.16 is a sum), `Sofic/ExactInvolutionCut.lean`
  (raw compressor audit), `Sofic/InvolutiveCentralizerComponents.lean` (sofic
  lane), `Sofic/CommutingLampCollapse.lean` (application),
  `Sofic/DefectSaturation.lean` (`thm:saturation`).
* `Kazhdan/HilbertCircumcenter.lean` exists but is **not** what the collapse
  uses: COL.29 runs on the sequence-level circumcenter of
  `Kazhdan/UltralimitGeometry.lean` (`orbitRadius`, `centerRadius`,
  `exists_near_center`, `seqNormSq_sub_le_of_near_center`), which is precisely
  the manuscript's "circumcenter … taken at the level of bounded sequences".
  That is the right primitive.

---

## 8. Resolution, 2026-08-16: S1–S3 and S5 are closed, and one repair was itself wrong

`thm:collapse` no longer prints a sketch.  Steps 5 and 6 now run in the
Hilbert-space ultraproduct of the `(M_{d_n}, Tr)`: the `b_n` assemble into an
exact 1-cocycle, Delorme–Guichardet (BHV Thm 2.12.4) makes it a coboundary,
`(W2)` gives `b(sas⁻¹) = 0` exactly because Step 1's family is indexed by the
orbit, and the transport theorem's own `Q = P` puts the primitive in
`Fix π(L)`.  That closes S1 (no operator-distance rigidity lemma is needed),
S2 (the coboundary is exact, so there is no tolerance to diagonalize), S3
(the limit is `lim_ω`, never a `limsup`) and S5 (the generator mass is used
as an exact identity, not as a bound).  S4 is closed by the correction lemma
with the explicit `3·15^m·ε` bound now printed in Step 1.

**A note for anyone re-auditing this section.**  Between those two states the
manuscript briefly carried a different repair (commit `e9563a3d`), which
replaced Step 6 with a one-stage argument on the grounds that the equality
`Fix π(sLs⁻¹) = Fix π(L)` "is supplied neither by Theorem 3.1 nor by
Theorem 6.1", and justified its own crux, the reverse-corner bound, "precisely
because `s` normalizes `L`".  Both halves are wrong, and it is worth recording
why, because each is an easy mistake to make twice.

1. **`s` does not normalize `L`.**  The construction turns on `tΓt⁻¹ ⊊ Γ`
   being strict; a normalizer would leave nothing to compress.  The Lean does
   not assume it: `KazhdanCompressionCore` carries the one-sided relation.
2. **The equality is supplied** — by the *proof* of the transport theorem, not
   by its statement.  The statement quantifies over a sequence `(x_n)`; the
   paragraph that derives `Q = P` does not mention one.  It builds `P` from the
   Kazhdan gap, identifies `ran π(s)Pπ(s)*` with `Fix π(sLs⁻¹)`, gets `P ≤ Q`
   from the one-sided inclusion, and closes with finiteness of the norm
   ultraproduct (now `lem:finitecompare` + `lem:ultrafinite`).  Reading a
   theorem's hypotheses as if they governed every step inside its proof is the
   trap here.
3. **What actually discharges the finite-stage `hrev`** is not a normalizer but
   the equal-rank reversal estimate.  `stage_transport_bound`
   (`InvolutionCollapseEndpoint.lean:444`) *takes* `hrev` as a hypothesis; the
   slot is filled inside `no_marked_model` by `h6`, built at
   `InvolutionCollapseEndpoint.lean:731-736` from
   `KazhdanCompressorCorner.one_sub_corner_mul_moved_vanishing`
   (`KazhdanCompressorCorner.lean:492`), and consumed at `:812`.  That lemma
   chains two things:
   - the easy containment, `one_sub_moved_mul_corner_vanishing` (`:407`), which
     factors `(1-Q)P = β(t)·[spectralBelow(H,θ)·(β(t)ᴴP)]` by unitarity alone
     (`:431-443`) and kills the below-threshold part via
     `rotated_laplacian_vanishing` (`:319`).  The compression field is touched
     in exactly one place, `one_sub_map_mul_rotated_vanishing:216`:
     `obtain ⟨δ, hrel⟩ := C.compresses s`.  Used as an equation, never
     inverted, never conjugated back by `t⁻¹`.  `δ ∈ ⟨S⟩` enters only through
     `hgen` and `Submonoid.closure_induction`; since `OpNormVanishing` is a
     per-element limit and only `|S|` many `δ` ever appear, no uniform
     word-length bound is needed or assumed.
   - `norm_one_sub_mul_flip` (`ProjectionRankFlip.lean:140-144`) at
     `movedProjection_rank = cornerProjection_rank`, the ranks agreeing only
     because `movedProjection = β(t)·P·β(t)ᴴ` is a unitary conjugate
     (`rank_unitary_conj`, `ProjectionRankFlip.lean:294`).

   That second step is stable finiteness, not a norm manipulation: the leakage
   bound makes the compression `range p → range q` injective (`:156-178`), and
   equal rank promotes injective to surjective through
   `LinearMap.injective_iff_surjective_of_finrank_eq_finrank` (`:180-183`).
   Equal rank is the finite-dimensional stand-in for the absent proper
   isometry — the same implication the three-column display at the head of
   Section 3 puts in its middle column.  Zero group-theoretic input.

The one-stage argument was kept: it is the content of
`rem:collapse-finite-stage`, with its constants, both corner estimates and all
three `InvolutionCollapseEndpoint` badges, and with the crux justified as in
(3).  Ledger consequence: those three badges now sit under
`rem:collapse-finite-stage` rather than `thm:collapse`, so `CO.11`–`CO.15`
need re-anchoring.

### 8.1 Where the axiom attestation for `thm:collapse` actually comes from

Traced because the badge is only as good as the check behind it.

* **The kernel-wide gate reaches it, with no exclusions.**
  `scripts/Audit.lean:633-635` folds `env.constants` for every name prefixed
  `GroupApproximation` — no `userWritten`, no `DeclFilter`, no exclusion list —
  and `:669-678` throws unless the union of axiom closures is contained in
  `{propext, Classical.choice, Quot.sound}`, with a `decls.size < 100`
  tripwire against an empty sweep.  `GroupApproximation.lean:290` imports
  `Sofic.InvolutionCollapseEndpoint`, so the endpoint is in the swept set.
  `Audit.Scan`'s population (`scripts/Audit/Scan.lean:84-86`) reaches it too,
  by module root rather than namespace; `DeclFilter`'s exclusions
  (`DeclFilter.lean:110-123`) match nothing here, and its own docstring
  (`:80-84`) records that those exclusions apply to the author-shape scans
  only, never to the axiom gate.
* **It is hard-gated in CI.**  `prover.yml:535-538` runs the audit with
  `continue-on-error: true`, and the verdict step at `:588-609` fails the job
  unless that step's outcome is `success`, counting `skipped` as failure.
* **One caveat, now closed.**  The independent nanoda re-check
  (`independent-kernel.yml:163-174`) exports only `headlineTheorems` as roots,
  and no collapse declaration was on that roster — so the collapse family had
  namespace-sweep coverage but no independent-kernel coverage except by
  accident of some other theorem's closure.  The four manuscript wrappers
  (`manuscriptInvolutiveCollapse`, `manuscriptNormalKazhdanObstruction`, its
  abstract form, `manuscriptDefectSaturation`) are now on the roster.  The
  workflow extracts it with `grep -oE '``[A-Za-z0-9_.]+'`, so the comment line
  added beside them is skipped.
* **What a `sorry` grep is worth here: nothing.**  Exactly one `sorry` token
  exists under `GroupApproximation/`, in a docstring
  (`Sofic/LiteralSoficAssembly.lean:8`), and there are no hand-declared
  `axiom`s — but that is a grep, and the attestation is the gate above.
