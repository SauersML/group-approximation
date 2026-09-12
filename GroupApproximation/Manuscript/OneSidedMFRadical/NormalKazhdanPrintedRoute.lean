import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedRouteAnalyticFacts
import GroupApproximation.Manuscript.OneSidedMFRadical.MaximalCStarTrivialCharacter
import GroupApproximation.Manuscript.OneSidedMFRadical.NormalKazhdan
import GroupApproximation.Manuscript.OneSidedMFRadical.ShadowResidual
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:normal-kazhdan` along the printed route

`non_mf_groups_exist.tex`, Theorem `thm:normal-kazhdan`:

> Let `G` be countable and let `K ⊴ G` have property (T).  If every operator
> norm asymptotic representation `(V_n)` of `G` satisfies `‖V_n(k) - 1‖₂ → 0`
> for all `k ∈ K`, then every corona homomorphism from `G` is trivial on `K`.

`Manuscript/OneSidedMFRadical/NormalKazhdan.lean` already carries that
statement as the closed proposition `NormalKazhdanRadical`, proved by the
development's own moving-corner detector.  The manuscript's *proof* was
rewritten to avoid ultrafilters, and this module proves the same closed
proposition a second time, following the printed sentences one by one:

1. the Kazhdan projection `e_K` of `C*_max(K)` and its image
   `p = f(e_K) ∈ 𝒬_d` under the homomorphism induced by `Θ|_K`;
2. `gKg⁻¹ = K` gives `Θ(g) p Θ(g)* = p` — the printed fixed-vector sentence,
   proved algebraically from the *two-sided* compression hypothesis that
   normality supplies, where one side alone gives only `Θ(g)* p Θ(g) ≤ p`;
3. `q = 1 - p ≠ 0` because `Θ` is nontrivial on `K`;
4. Lemma `lem:central-corona-corner` produces `W_n` whose corona class is the
   coordinate restriction of `g ↦ q Θ(g)`;
5. `π(e_K)` is the coordinate restriction of `q p = 0`;
6. density of `ℂ[K]` in `C*_max(K)`: a finite `F ⊆ K` and scalars `α` with
   `‖a - e_K‖ < 1/4`;
7. the trivial character gives `|Σ α_k - 1| < 1/4`;
8. `limsup_n ‖Σ α_k W_n(k)‖ = ‖π(a)‖ = ‖π(a - e_K)‖ < 1/4`;
9. the Hilbert--Schmidt hypothesis applies to `(W_n)`, so
   `|tr_{r_n}(W_n(k)) - 1| ≤ ‖W_n(k) - I_{r_n}‖₂ → 0`;
10. hence `tr_{r_n}(Σ α_k W_n(k)) → Σ α_k`;
11. and `|tr_{r_n}(x)| ≤ ‖x‖` makes the limit at most `1/4` while
    `|Σ α_k| > 3/4`, a contradiction.

The old carrier `manuscriptNormalKazhdanRadical` and its sentence module
`NormalKazhdanSentences.lean` are untouched: they transcribe the *previous*
printed proof, which went through the Kazhdan inequality `b ≥ (κ²/|S|)1` and a
surviving `s₀ ∈ S`.  Neither sentence of that argument occurs in the printed
proof any more.

The step the printed proof states as a fact about a faithful representation —
"`p` is the projection onto the `K`-fixed vectors", so the two ranges of
`Θ(g) p Θ(g)*` and `p` agree — is carried here by
`Analysis/MaximalCStarKazhdanProjection.lean`'s absorption calculus instead:
`conj_image_mul_image` and `star_conj_image_mul_image` are exactly the two
range inclusions, and normality is what makes both of them available.  No
faithful representation of the corona is constructed, and none is needed.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace NormalKazhdanPrintedRoute

open Filter Matrix Topology
open MaximalCStarKazhdanProjection
open PrintedCornerCompression
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ## Sentence 1: the Kazhdan projection and its image -/

/-- **`thm:normal-kazhdan`, printed sentence.**

> Let `e_K ∈ C*_max(K)` be the Kazhdan projection of `K`, and let
> `p ∈ 𝒬_d` be its image under the homomorphism `C*_max(K) → 𝒬_d` induced by
> `Θ|_K`.

The homomorphism is the one the universal property of `C*_max(K)` supplies,
and `p` is a projection of the target fixed by every `Θ(k)` — the algebraic
half of the printed "in any faithful representation `p` is the projection onto
the `K`-fixed vectors". -/
theorem manuscriptSentence_kazhdanProjectionImage
    {L : Type} [Group L] {B : Type} [CStarAlgebra B] (KD : KazhdanData L)
    (T : L →* unitary B) :
    ∃ f : MaximalGroupCStar L →⋆ₐ[ℂ] B,
      (∀ s : L, f (maximalGroupCStarGenerator L s) = ((T s : unitary B) : B)) ∧
        IsSelfAdjoint (f KD.projection) ∧
        f KD.projection * f KD.projection = f KD.projection ∧
        ∀ s : L, ((T s : unitary B) : B) * f KD.projection = f KD.projection := by
  obtain ⟨f, hf, -⟩ := maximalGroupCStar_existsUnique_lift_allUniverses L T
  exact ⟨f, hf, isSelfAdjoint_image KD f, image_mul_image KD f,
    fun s ↦ rep_mul_image KD T f hf s⟩

/-! ## Sentence 2: normality, and the two ranges -/

/-- **`thm:normal-kazhdan`, printed sentence.**

> Since `gKg⁻¹ = K`, ...

Normality is used exactly here, and it is used twice: `gKg⁻¹ ⊆ K` gives the
printed compression hypothesis for `Θ(g)`, and `g⁻¹Kg ⊆ K` gives it for
`Θ(g)*`.  One of the two alone would give only an inequality of projections. -/
theorem manuscriptSentence_normalityGivesBothCompressions
    {G : Type} [Group G] {B : Type} [CStarAlgebra B] (K : Subgroup G)
    [hKn : K.Normal] (Theta : G →* unitary B) (g : G) :
    (∀ s : ↥K, ∃ t : ↥K,
        ((Theta g : unitary B) : B) * ((Theta ((s : G)) : unitary B) : B)
            * star ((Theta g : unitary B) : B)
          = ((Theta ((t : G)) : unitary B) : B)) ∧
      (∀ s : ↥K, ∃ t : ↥K,
        star ((Theta g : unitary B) : B) * ((Theta ((s : G)) : unitary B) : B)
            * ((Theta g : unitary B) : B)
          = ((Theta ((t : G)) : unitary B) : B)) := by
  have hstar : ∀ h : G, ((Theta h⁻¹ : unitary B) : B)
      = star ((Theta h : unitary B) : B) := by
    intro h
    have h1 : Theta h⁻¹ = star (Theta h) := by
      rw [map_inv, Unitary.star_eq_inv]
    rw [h1, Unitary.coe_star]
  constructor
  · intro s
    refine ⟨⟨g * (s : G) * g⁻¹, hKn.conj_mem (s : G) s.2 g⟩, ?_⟩
    have h1 : Theta (g * (s : G) * g⁻¹)
        = Theta g * Theta ((s : G)) * Theta g⁻¹ := by
      rw [map_mul, map_mul]
    have h2 : ((Theta g * Theta ((s : G)) * Theta g⁻¹ : unitary B) : B)
        = ((Theta g : unitary B) : B) * ((Theta ((s : G)) : unitary B) : B)
          * ((Theta g⁻¹ : unitary B) : B) := rfl
    rw [h1, h2, hstar g]
  · intro s
    have hmem : g⁻¹ * (s : G) * g ∈ K := by
      have h := hKn.conj_mem (s : G) s.2 g⁻¹
      rwa [inv_inv] at h
    refine ⟨⟨g⁻¹ * (s : G) * g, hmem⟩, ?_⟩
    have h1 : Theta (g⁻¹ * (s : G) * g)
        = Theta g⁻¹ * Theta ((s : G)) * Theta g := by
      rw [map_mul, map_mul]
    have h2 : ((Theta g⁻¹ * Theta ((s : G)) * Theta g : unitary B) : B)
        = ((Theta g⁻¹ : unitary B) : B) * ((Theta ((s : G)) : unitary B) : B)
          * ((Theta g : unitary B) : B) := rfl
    rw [h1, h2, hstar g]

/-- **`thm:normal-kazhdan`, printed sentence.**

> In any faithful representation of the corona, `p` is the projection onto the
> `K`-fixed vectors.  Since `gKg⁻¹ = K`, the range of `Θ(g) p Θ(g)*` is
> `Θ(g) Fix Θ(K) = Fix Θ(gKg⁻¹) = Fix Θ(K)`, so `Θ(g) p Θ(g)* = p`.

The printed sentence names two ranges and asserts that they agree.  Here the
two range inclusions are the two absorption identities of
`Analysis/MaximalCStarKazhdanProjection.lean`: `star_conj_image_mul_image` at
`U` is `ran(U* p U) ⊆ ran p`, and `conj_image_mul_image` at `U*` — available
only because normality compresses `Θ(K)` by `U*` as well — is the reverse.
No faithful representation is constructed. -/
theorem manuscriptSentence_conjugateFixesKazhdanImage
    {L : Type} [Group L] {B : Type} [CStarAlgebra B] (KD : KazhdanData L)
    (T : L →* unitary B) (f : MaximalGroupCStar L →⋆ₐ[ℂ] B)
    (hf : ∀ s : L, f (maximalGroupCStarGenerator L s) = ((T s : unitary B) : B))
    (U : B) (hU : star U * U = 1) (hU' : U * star U = 1)
    (hcomp : ∀ s : L, ∃ t : L,
      U * ((T s : unitary B) : B) * star U = ((T t : unitary B) : B))
    (hcomp' : ∀ s : L, ∃ t : L,
      star U * ((T s : unitary B) : B) * U = ((T t : unitary B) : B)) :
    U * f KD.projection * star U = f KD.projection ∧
      star U * f KD.projection * U = f KD.projection := by
  have h1 : (star U * f KD.projection * star (star U)) * f KD.projection
      = f KD.projection :=
    conj_image_mul_image KD T f hf (star U)
      (by rw [star_star]; exact hU') (by rw [star_star]; exact hU)
      (by
        intro s
        rw [star_star]
        exact hcomp' s)
  rw [star_star] at h1
  have h2 := star_conj_image_mul_image KD T f hf U hU hU' hcomp
  have hkey : star U * f KD.projection * U = f KD.projection := h2.symm.trans h1
  refine ⟨?_, hkey⟩
  calc U * f KD.projection * star U
      = U * (star U * f KD.projection * U) * star U := by rw [hkey]
    _ = (U * star U) * f KD.projection * (U * star U) := by noncomm_ring
    _ = f KD.projection := by rw [hU', one_mul, mul_one]

/-! ## Sentence 3: the complement is a nonzero central projection -/

/-- **`thm:normal-kazhdan`, printed sentence.**

> ... and `q = 1 - p` is nonzero because `Θ` is nontrivial on `K`.

If `q` were zero then `p` would be `1`, and `Θ(k) p = p` would read
`Θ(k) = 1` for every `k ∈ K`. -/
theorem manuscriptSentence_complementNonzero
    {L : Type} [Group L] {B : Type} [CStarAlgebra B] (KD : KazhdanData L)
    (T : L →* unitary B) (f : MaximalGroupCStar L →⋆ₐ[ℂ] B)
    (hf : ∀ s : L, f (maximalGroupCStarGenerator L s) = ((T s : unitary B) : B))
    {s0 : L} (hs0 : T s0 ≠ 1) :
    (1 : B) - f KD.projection ≠ 0 := by
  intro h0
  have hp : f KD.projection = 1 := (sub_eq_zero.mp h0).symm
  have hfix := rep_mul_image KD T f hf s0
  rw [hp, mul_one] at hfix
  exact hs0 (Subtype.ext hfix)

/-- **`thm:normal-kazhdan`, printed sentence.**

> ... `Θ(g) p Θ(g)* = p` for all `g ∈ G`, and `q = 1 - p` ...

`q` is a projection commuting with `Θ(G)` and annihilating `p`, which is
exactly the package Lemma `lem:central-corona-corner` consumes and the package
the norm estimate of sentence 8 consumes. -/
theorem manuscriptSentence_complementIsCentralProjection
    {B : Type} [CStarAlgebra B] {p : B} (hpsa : IsSelfAdjoint p)
    (hpid : p * p = p) {ι : Type*} (u : ι → B)
    (hconj : ∀ i, u i * p * star (u i) = p)
    (hu : ∀ i, star (u i) * u i = 1) :
    IsStarProjection ((1 : B) - p) ∧
      ((1 : B) - p) * p = 0 ∧
      (∀ y : B, ((1 : B) - p) * y = ((1 : B) - p) * (y - p)) ∧
      ∀ i, u i * ((1 : B) - p) = ((1 : B) - p) * u i := by
  have hzero : ((1 : B) - p) * p = 0 := by
    rw [sub_mul, one_mul, hpid, sub_self]
  refine ⟨⟨?_, ?_⟩, hzero, ?_, ?_⟩
  · show ((1 : B) - p) * ((1 : B) - p) = (1 : B) - p
    rw [mul_sub, hzero, sub_zero, mul_one]
  · show star ((1 : B) - p) = (1 : B) - p
    rw [star_sub, star_one, hpsa.star_eq]
  · intro y
    rw [mul_sub, hzero, sub_zero]
  · intro i
    have hcomm : u i * p = p * u i := by
      calc u i * p = u i * p * (star (u i) * u i) := by rw [hu i, mul_one]
        _ = (u i * p * star (u i)) * u i := by noncomm_ring
        _ = p * u i := by rw [hconj i]
    rw [mul_sub, sub_mul, mul_one, one_mul, hcomm]

/-! ## Sentence 5: the Kazhdan projection dies in the corner corona -/

/-- **`thm:normal-kazhdan`, printed sentence.**

> Since `q` commutes with `Θ(K)`, the map `a ↦ q Θ(a)` is a homomorphism on
> `C*_max(K)` agreeing with `π` on `K`, so `π(e_K)` is the coordinate
> restriction of `q p = 0`.

The two clauses.  The first is the agreement on `K`: the corona class of the
corner representation at `k` is the coordinate restriction of `q Θ(k)`, which
is `q f(u_k)`.  The second is `q f(e_K) = q p = 0`, so the coordinate
restriction of `q f(e_K)` vanishes. -/
theorem manuscriptSentence_cornerCoronaKillsKazhdanProjection
    {G : Type} [Group G] {L : Type} [Group L]
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (rho : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n)))
    (KD : KazhdanData L)
    (f : MaximalGroupCStar L →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n))
    (iota : L →* G)
    (hf : ∀ s : L, f (maximalGroupCStarGenerator L s)
      = ((rho (iota s) : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n)))
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (D : PrintedCornerData G (fun k ↦ X (φ k)))
    (hclass : ∀ g : G,
      normMatrixCStarCoronaMk (fun k ↦ X (φ k)) (ambientCornerSeq D g)
        = coronaRestrict X φ hφ
            ((1 - f KD.projection) *
              ((rho g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
                NormMatrixCStarCorona (fun n ↦ X n)))) :
    (∀ s : L,
        normMatrixCStarCoronaMk (fun k ↦ X (φ k))
            (ambientCornerSeq D (iota s))
          = coronaRestrictAlg X φ hφ
              ((1 - f KD.projection) * f (maximalGroupCStarGenerator L s))) ∧
      coronaRestrictAlg X φ hφ ((1 - f KD.projection) * f KD.projection) = 0 := by
  refine ⟨?_, ?_⟩
  · intro s
    rw [hclass (iota s), hf s]
    rfl
  · have hzero : ((1 : NormMatrixCStarCorona (fun n ↦ X n)) - f KD.projection)
        * f KD.projection = 0 :=
      (manuscriptSentence_complementIsCentralProjection (isSelfAdjoint_image KD f)
        (image_mul_image KD f) (fun _ : Empty ↦ (0 : NormMatrixCStarCorona
          (fun n ↦ X n))) (fun i ↦ i.elim) (fun i ↦ i.elim)).2.1
    rw [hzero, map_zero]

/-! ## Sentences 6 and 7: density and the trivial character -/

/-- **`thm:normal-kazhdan`, printed sentence.**

> The group algebra `ℂ[K]` is dense in `C*_max(K)`, so there are a finite set
> `F ⊆ K` and scalars `(α_k)_{k∈F}` with `a = Σ α_k u_k`, `‖a - e_K‖ < 1/4`.
> The trivial character `χ` of `K`, the state of `C*_max(K)` with `χ(u_k) = 1`
> for every `k`, has `χ(e_K) = 1`, so `|Σ α_k - 1| = |χ(a - e_K)| < 1/4`. -/
theorem manuscriptSentence_denseCombinationAndCharacter
    {L : Type} [Group L] (KD : KazhdanData L) :
    ∃ (F : Finset L) (alpha : L → ℂ),
      ‖(∑ s ∈ F, alpha s • maximalGroupCStarGenerator L s)
          - KD.projection‖ < 1 / 4 ∧
        ‖(∑ s ∈ F, alpha s) - 1‖ < 1 / 4 ∧
        (3 : ℝ) / 4 < ‖∑ s ∈ F, alpha s‖ := by
  obtain ⟨F, alpha, hclose⟩ :=
    exists_generatorCombination_close (K := L) KD.projection
      (by norm_num : (0 : ℝ) < 1 / 4)
  have hchi : maximalGroupCStarTrivialCharacter L
      ((∑ s ∈ F, alpha s • maximalGroupCStarGenerator L s) - KD.projection)
      = (∑ s ∈ F, alpha s) - 1 := by
    rw [map_sub, maximalGroupCStarTrivialCharacter_kazhdanProjection KD, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [map_smul, maximalGroupCStarTrivialCharacter_generator, smul_eq_mul,
      mul_one]
  have hlt : ‖(∑ s ∈ F, alpha s) - 1‖ < 1 / 4 := by
    rw [← hchi]
    exact lt_of_le_of_lt
      (NonUnitalStarAlgHom.norm_apply_le (maximalGroupCStarTrivialCharacter L) _)
      hclose
  refine ⟨F, alpha, hclose, hlt, ?_⟩
  have h1 : ‖(1 : ℂ)‖ - ‖∑ s ∈ F, alpha s‖ ≤ ‖(1 : ℂ) - ∑ s ∈ F, alpha s‖ :=
    norm_sub_norm_le _ _
  rw [norm_one, norm_sub_rev] at h1
  linarith

/-! ## Sentence 8: the corner combination has small corona norm -/

/-- The coordinates of a printed finite combination of corner unitaries, read
inside the ambient matrices. -/
theorem sum_smul_ambientCornerSeq_apply {G : Type*} [Group G]
    {model : ℕ → FiniteModel} (D : PrintedCornerData G model)
    {ι : Type*} (F : Finset ι) (alpha : ι → ℂ) (v : ι → G) (k : ℕ) :
    ((∑ s ∈ F, alpha s • ambientCornerSeq D (v s) :
        BoundedMatrixSequence (fun n ↦ model n)) :
          ∀ n, Matrix (model n) (model n) ℂ) k
      = ∑ s ∈ F, alpha s • ambientCornerMap D k (v s) := by
  classical
  refine Finset.induction_on F ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, lp.coeFn_zero, Pi.zero_apply]
  · intro b s hb ih
    rw [Finset.sum_insert hb, Finset.sum_insert hb, lp.coeFn_add, Pi.add_apply,
      ih, lp.coeFn_smul, Pi.smul_apply, ambientCornerSeq_apply]

/-- **`thm:normal-kazhdan`, printed sentence.**

> Since `π(e_K) = 0`,
> `limsup_n ‖Σ α_k W_n(k)‖ = ‖π(a)‖ = ‖π(a - e_K)‖ < 1/4`.

The quotient norm of the corner corona is the `limsup` of the coordinate
operator norms, and the corner embedding is an isometry, so the printed
`limsup` is the norm of the coordinate restriction of `q f(a)`.  Since
`q f(e_K) = 0` that equals the norm of the coordinate restriction of
`q f(a - e_K)`, which the three contractions bound by `‖a - e_K‖`. -/
theorem manuscriptSentence_limsupCombinationLtQuarter
    {G : Type} [Group G] {L : Type} [Group L]
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (rho : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n)))
    (KD : KazhdanData L)
    (f : MaximalGroupCStar L →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n))
    (iota : L →* G)
    (hf : ∀ s : L, f (maximalGroupCStarGenerator L s)
      = ((rho (iota s) : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n)))
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (D : PrintedCornerData G (fun k ↦ X (φ k)))
    (hclass : ∀ g : G,
      normMatrixCStarCoronaMk (fun k ↦ X (φ k)) (ambientCornerSeq D g)
        = coronaRestrict X φ hφ
            ((1 - f KD.projection) *
              ((rho g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
                NormMatrixCStarCorona (fun n ↦ X n))))
    (F : Finset L) (alpha : L → ℂ)
    (hclose : ‖(∑ s ∈ F, alpha s • maximalGroupCStarGenerator L s)
      - KD.projection‖ < 1 / 4) :
    Filter.limsup
        (fun k ↦ ‖∑ s ∈ F, alpha s •
          (D.cornerMap k (iota s) :
            Matrix (D.cornerModel k) (D.cornerModel k) ℂ)‖)
        Filter.cofinite < 1 / 4 := by
  classical
  obtain ⟨hsp, -, hsub, -⟩ :=
    manuscriptSentence_complementIsCentralProjection (isSelfAdjoint_image KD f)
      (image_mul_image KD f)
      (fun _ : Empty ↦ (0 : NormMatrixCStarCorona (fun n ↦ X n)))
      (fun i ↦ i.elim) (fun i ↦ i.elim)
  obtain ⟨hagree, -⟩ :=
    manuscriptSentence_cornerCoronaKillsKazhdanProjection X rho KD f iota hf
      φ hφ D hclass
  obtain ⟨Comb, hCombdef⟩ :
      ∃ c : BoundedMatrixSequence (fun k ↦ X (φ k)),
        c = ∑ s ∈ F, alpha s • ambientCornerSeq D (iota s) := ⟨_, rfl⟩
  -- the coordinatewise identification of the printed combination
  have hCombNorm : ∀ k : ℕ,
      ‖(Comb : ∀ k, Matrix (X (φ k)) (X (φ k)) ℂ) k‖
        = ‖∑ s ∈ F, alpha s •
            (D.cornerMap k (iota s) :
              Matrix (D.cornerModel k) (D.cornerModel k) ℂ)‖ := by
    intro k
    rw [hCombdef, sum_smul_ambientCornerSeq_apply D F alpha (fun s ↦ iota s) k]
    have h1 : (∑ s ∈ F, alpha s • ambientCornerMap D k (iota s))
        = cornerEmbed (D.qHermitian k)
            (∑ s ∈ F, alpha s •
              (D.cornerMap k (iota s) :
                Matrix (D.cornerModel k) (D.cornerModel k) ℂ)) := by
      rw [cornerEmbed_sum_smul]
      exact Finset.sum_congr rfl fun s _ ↦ rfl
    rw [h1, norm_cornerEmbed]
  -- the corona class of the printed combination
  have hmk : normMatrixCStarCoronaMk (fun k ↦ X (φ k)) Comb
      = coronaRestrictAlg X φ hφ
          ((1 - f KD.projection) *
            f (∑ s ∈ F, alpha s • maximalGroupCStarGenerator L s)) := by
    have hstep1 : normMatrixCStarCoronaMk (fun k ↦ X (φ k)) Comb
        = ∑ s ∈ F, alpha s • normMatrixCStarCoronaMk (fun k ↦ X (φ k))
            (ambientCornerSeq D (iota s)) := by
      rw [hCombdef]
      show normMatrixCStarCoronaQuotient (fun k ↦ X (φ k)) _ = _
      rw [map_sum]
      exact Finset.sum_congr rfl fun s _ ↦ map_smul _ _ _
    rw [hstep1]
    calc ∑ s ∈ F, alpha s • normMatrixCStarCoronaMk (fun k ↦ X (φ k))
            (ambientCornerSeq D (iota s))
        = ∑ s ∈ F, coronaRestrictAlg X φ hφ
            (alpha s • ((1 - f KD.projection) *
              f (maximalGroupCStarGenerator L s))) := by
          refine Finset.sum_congr rfl fun s _ ↦ ?_
          rw [hagree s, map_smul]
      _ = coronaRestrictAlg X φ hφ
            (∑ s ∈ F, alpha s • ((1 - f KD.projection) *
              f (maximalGroupCStarGenerator L s))) := (map_sum _ _ _).symm
      _ = coronaRestrictAlg X φ hφ
            ((1 - f KD.projection) *
              f (∑ s ∈ F, alpha s • maximalGroupCStarGenerator L s)) := by
          congr 1
          rw [map_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun s _ ↦ by
            rw [map_smul, mul_smul_comm]
  -- the printed norm estimate
  have hnormlt : ‖coronaRestrictAlg X φ hφ
      ((1 - f KD.projection) *
        f (∑ s ∈ F, alpha s • maximalGroupCStarGenerator L s))‖ < 1 / 4 := by
    have hrewrite : ((1 : NormMatrixCStarCorona (fun n ↦ X n))
          - f KD.projection) *
          f (∑ s ∈ F, alpha s • maximalGroupCStarGenerator L s)
        = ((1 : NormMatrixCStarCorona (fun n ↦ X n)) - f KD.projection) *
          f ((∑ s ∈ F, alpha s • maximalGroupCStarGenerator L s)
            - KD.projection) := by
      rw [map_sub]
      exact hsub (f (∑ s ∈ F, alpha s • maximalGroupCStarGenerator L s))
    rw [hrewrite]
    calc ‖coronaRestrictAlg X φ hφ
            (((1 : NormMatrixCStarCorona (fun n ↦ X n)) - f KD.projection) *
              f ((∑ s ∈ F, alpha s • maximalGroupCStarGenerator L s)
                - KD.projection))‖
        ≤ ‖((1 : NormMatrixCStarCorona (fun n ↦ X n)) - f KD.projection) *
            f ((∑ s ∈ F, alpha s • maximalGroupCStarGenerator L s)
              - KD.projection)‖ := norm_coronaRestrictAlg_le X φ hφ _
      _ ≤ ‖(1 : NormMatrixCStarCorona (fun n ↦ X n)) - f KD.projection‖ *
            ‖f ((∑ s ∈ F, alpha s • maximalGroupCStarGenerator L s)
              - KD.projection)‖ := norm_mul_le _ _
      _ ≤ 1 * ‖(∑ s ∈ F, alpha s • maximalGroupCStarGenerator L s)
              - KD.projection‖ :=
            mul_le_mul (IsStarProjection.norm_le _ hsp)
              (NonUnitalStarAlgHom.norm_apply_le f _) (norm_nonneg _)
              zero_le_one
      _ < 1 / 4 := by rw [one_mul]; exact hclose
  have hnorm : ‖normMatrixCStarCoronaMk (fun k ↦ X (φ k)) Comb‖ < 1 / 4 := by
    rw [hmk]; exact hnormlt
  rw [norm_normMatrixCStarCoronaMk_eq_limsup (fun k ↦ X (φ k)) Comb] at hnorm
  have hcongr : (fun k ↦ ‖∑ s ∈ F, alpha s •
        (D.cornerMap k (iota s) :
          Matrix (D.cornerModel k) (D.cornerModel k) ℂ)‖)
      = fun k ↦ ‖(Comb : ∀ k, Matrix (X (φ k)) (X (φ k)) ℂ) k‖ := by
    funext k
    exact (hCombNorm k).symm
  rw [hcongr]
  exact hnorm

/-! ## Sentences 9 and 10: the trace of the printed combination -/

/-- **`thm:normal-kazhdan`, printed sentence.**

> The hypothesis applies to `(W_n)` itself, so
> `|tr_{r_n}(W_n(k)) - 1| ≤ ‖W_n(k) - I_{r_n}‖₂ → 0` for `k ∈ K`,
> and then `tr_{r_n}(Σ α_k W_n(k)) → Σ α_k`.

The hypothesis is `K ≤ R_{∞→2}(G)`, whose printed reading
(`ShadowResidual.mem_opToHSShadowResidual_iff_forall_hsKernel`) is exactly
`‖W_n(k) - I‖₂ → 0` for the corner representation `W`. -/
theorem manuscriptSentence_traceOfCombinationTendsTo
    {G : Type} [Group G] {L : Type} [Group L] (iota : L →* G)
    (hres : ∀ s : L, iota s ∈ opToHSShadowResidual G)
    {model : ℕ → FiniteModel} (D : PrintedCornerData G model)
    (F : Finset L) (alpha : L → ℂ) :
    (∀ s : L, Filter.Tendsto
        (fun k ↦ normTrace (D.cornerModel k)
          ((D.cornerMap k (iota s) :
            Matrix (D.cornerModel k) (D.cornerModel k) ℂ)))
        Filter.atTop (nhds 1)) ∧
      Filter.Tendsto
        (fun k ↦ normTrace (D.cornerModel k)
          (∑ s ∈ F, alpha s •
            (D.cornerMap k (iota s) :
              Matrix (D.cornerModel k) (D.cornerModel k) ℂ)))
        Filter.atTop (nhds (∑ s ∈ F, alpha s)) := by
  have hHS : ∀ s : L, Filter.Tendsto
      (fun k ↦ normTrace (D.cornerModel k)
        ((D.cornerMap k (iota s) :
          Matrix (D.cornerModel k) (D.cornerModel k) ℂ)))
      Filter.atTop (nhds 1) := by
    intro s
    have hker : iota s ∈ hsKernel D.cornerRepresentation :=
      (mem_opToHSShadowResidual_iff_forall_hsKernel (iota s)).mp (hres s)
        D.cornerRepresentation
    have hnull : IsHSNull D.cornerRepresentation (iota s) := hker
    have htend :=
      (isHSNull_iff_tendsto D.cornerRepresentation (iota s)).mp hnull
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun k ↦ norm_nonneg _) (fun k ↦ ?_) htend
    exact norm_normTrace_sub_one_le (D.cornerModel k)
      (D.cornerModel_card_pos k) _
  refine ⟨hHS, ?_⟩
  have h1 : ∀ k : ℕ, normTrace (D.cornerModel k)
      (∑ s ∈ F, alpha s •
        (D.cornerMap k (iota s) :
          Matrix (D.cornerModel k) (D.cornerModel k) ℂ))
      = ∑ s ∈ F, alpha s * normTrace (D.cornerModel k)
          ((D.cornerMap k (iota s) :
            Matrix (D.cornerModel k) (D.cornerModel k) ℂ)) :=
    fun k ↦ normTrace_sum_smul _ F alpha _
  simp only [h1]
  have h2 : (∑ s ∈ F, alpha s) = ∑ s ∈ F, alpha s * 1 := by
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [mul_one]
  rw [h2]
  exact tendsto_finsetSum F fun s _ ↦ (hHS s).const_mul (alpha s)

/-! ## The endpoint -/

/-- **Theorem `thm:normal-kazhdan`, proved along the printed route.**

The same closed proposition as `manuscriptNormalKazhdanRadical`, proved by the
sentences above rather than by the development's moving-corner detector. -/
theorem manuscriptNormalKazhdanRadical_printedRoute : NormalKazhdanRadical := by
  classical
  intro G _ _ K _ hT hKres k0 hk0
  show ActualCoronaMFInvisible k0
  intro X hX
  letI : ∀ n, Nonempty (X n) := fun n ↦ Fintype.card_pos_iff.mp (hX n)
  intro rho
  by_contra hne
  obtain ⟨KD⟩ := exists_kazhdanData ↥K hT
  obtain ⟨f, hf, hpsa, hpid, -⟩ :=
    manuscriptSentence_kazhdanProjectionImage KD (rho.comp K.subtype)
  -- sentence 2: normality gives both compressions, hence `Θ(g) p Θ(g)* = p`
  have hconj : ∀ g : G,
      ((rho g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n)) * f KD.projection
        * star ((rho g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
            NormMatrixCStarCorona (fun n ↦ X n)) = f KD.projection := by
    intro g
    obtain ⟨hc1, hc2⟩ :=
      manuscriptSentence_normalityGivesBothCompressions K rho g
    exact (manuscriptSentence_conjugateFixesKazhdanImage KD
      (rho.comp K.subtype) f hf _
      (Unitary.star_mul_self_of_mem (rho g).2)
      (Unitary.mul_star_self_of_mem (rho g).2) hc1 hc2).1
  -- sentence 3: `q = 1 - p` is a nonzero central projection
  obtain ⟨hsp, -, -, hqcomm⟩ :=
    manuscriptSentence_complementIsCentralProjection hpsa hpid
      (fun g : G ↦ ((rho g : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
        NormMatrixCStarCorona (fun n ↦ X n))) hconj
      (fun g ↦ Unitary.star_mul_self_of_mem (rho g).2)
  have hqne : (1 : NormMatrixCStarCorona (fun n ↦ X n)) - f KD.projection ≠ 0 :=
    manuscriptSentence_complementNonzero KD (rho.comp K.subtype) f hf
      (s0 := ⟨k0, hk0⟩) hne
  -- sentence 4: the corner representation and its corona class
  obtain ⟨φ, hφ, Qlift, D, -, -, -, -, -, -, hclass⟩ :=
    manuscriptCornerCoronaClass G X rho
      ((1 : NormMatrixCStarCorona (fun n ↦ X n)) - f KD.projection)
      hsp.isSelfAdjoint hsp.isIdempotentElem hqne hqcomm
  -- sentences 6 and 7
  obtain ⟨F, alpha, hclose, -, hbig⟩ :=
    manuscriptSentence_denseCombinationAndCharacter (L := ↥K) KD
  -- sentence 8
  have hlimsup := manuscriptSentence_limsupCombinationLtQuarter X rho KD f
    K.subtype hf φ hφ D hclass F alpha hclose
  -- sentences 9 and 10
  obtain ⟨-, htrace⟩ :=
    manuscriptSentence_traceOfCombinationTendsTo (K.subtype) (fun s ↦ hKres s.2)
      D F alpha
  -- sentence 11
  have hbdd : Filter.IsBoundedUnder (· ≤ ·) Filter.cofinite
      (fun k ↦ ‖∑ s ∈ F, alpha s •
        (D.cornerMap k (K.subtype s) :
          Matrix (D.cornerModel k) (D.cornerModel k) ℂ)‖) := by
    refine Filter.isBoundedUnder_of ⟨∑ s ∈ F, ‖alpha s‖, fun k ↦ ?_⟩
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun s _ ↦ ?_)
    rw [norm_smul]
    calc ‖alpha s‖ * ‖(D.cornerMap k (K.subtype s) :
            Matrix (D.cornerModel k) (D.cornerModel k) ℂ)‖
        ≤ ‖alpha s‖ * 1 :=
          mul_le_mul_of_nonneg_left
            (D.norm_cornerMap_le_one k (K.subtype s)) (norm_nonneg _)
      _ = ‖alpha s‖ := mul_one _
  have hev : ∀ᶠ k in Filter.cofinite, ‖∑ s ∈ F, alpha s •
      (D.cornerMap k (K.subtype s) :
        Matrix (D.cornerModel k) (D.cornerModel k) ℂ)‖ < 1 / 4 :=
    Filter.eventually_lt_of_limsup_lt hlimsup hbdd
  rw [Nat.cofinite_eq_atTop] at hev
  have hlimit : ‖∑ s ∈ F, alpha s‖ ≤ 1 / 4 := by
    refine le_of_tendsto htrace.norm ?_
    filter_upwards [hev] with k hk
    exact le_trans (PrintedPreliminaryEstimates.norm_normTrace_le_l2_opNorm
      (D.cornerModel k) _) hk.le
  linarith

end

end NormalKazhdanPrintedRoute
end OneSidedMFRadical
end Manuscript
end GroupApproximation

open GroupApproximation

#audit_closed_axioms
  Manuscript.OneSidedMFRadical.NormalKazhdanPrintedRoute.manuscriptNormalKazhdanRadical_printedRoute
