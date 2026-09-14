import GroupApproximation.Manuscript.NinetyNineProblems.FactorizationProperty
import GroupApproximation.Analysis.KirchbergTraceModels
import GroupApproximation.Analysis.KirchbergRealDilation
import GroupApproximation.Analysis.KirchbergTensorSquare
import GroupApproximation.Kazhdan.KazhdanNearInvariantVector
import GroupApproximation.Kazhdan.KazhdanFiniteGeneration
import GroupApproximation.Algebra.OrthogonalRepresentationResiduallyFinite
import GroupApproximation.Meta.AxiomGuard

/-!
# Kirchberg's Theorem 1.1, proved

> Kirchberg, *Discrete groups with Kazhdan's property T and factorization
> property are residually finite*, Math. Ann. **299** (1994), Theorem 1.1.

This module inhabits `NinetyNineProblems.KirchbergKazhdanFactorizationInput`
at the trace side of the factorization property, which is the repository's
definition (`HasFactorizationProperty`).  No input is assumed.

Let `h ≠ 1`, let `(Q, ε)` be a Kazhdan pair, and let `Xₙ(g) = φₙ(u_g)` be the
matrix models of the amenable canonical trace.

1. At one index, `Re tr (Xₙ(q)ᴴ Xₙ(q)) / k ≈ 1` for `q ∈ Q` and
   `Re tr Xₙ(h) / k ≈ 0` (`KirchbergTraceModels.exists_index`).
2. `Xₙ` is a positive definite matrix function.  Its real dilation `K` carries
   an orthogonal representation `σ` and an orthonormal frame
   `e_a = V β_a` with `⟪e_a, σ(g) e_b⟫ = Re ⟪β_a, Xₙ(g) β_b⟫`
   (`KirchbergRealDilation`).
3. `η = (2k)^{-1/2} ∑ₐ e_a ⊗ e_a` is a unit vector of `K ⊗̂ K` with
   `⟪(σ ⊗ σ)(q) η, η⟫ = Re tr (Xₙ(q)ᴴ Xₙ(q)) / k`, so it is almost invariant.
   The Kazhdan pair gives an invariant `ζ` within `1/4` of `η`
   (`KazhdanNearInvariantVector`).
4. If `h` fixed every finite-dimensional subrepresentation of `σ`, compact
   extraction would give `⟪ζ, (σ(h) ⊗ 1) η⟫ = ⟪ζ, η⟫`
   (`KirchbergTensorSquare.inner_tmulC_of_forall_fixed`).  The left side is
   within `1/4` of `⟪η, (σ(h) ⊗ 1) η⟫ = Re tr Xₙ(h) / k ≈ 0`, and the right side
   within `1/4` of `1`.
5. So `h` acts nontrivially in a finite-dimensional orthogonal representation.
   `G` is finitely generated, and Mal'cev's theorem makes it residually finite
   (`OrthogonalRepresentationResiduallyFinite`).
-/

namespace GroupApproximation
namespace NinetyNineProblems
namespace KirchbergTheorem

open Matrix KirchbergRealForms KirchbergRealDilation KirchbergTensorSquare
  KirchbergCompactExtraction AmenableTraceHyperlinear

universe u

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-! ## The frame and the almost invariant vector -/

section Frame

variable {G : Type u} [Group G] {Y : Type} [Fintype Y] [DecidableEq Y]
variable (X : G → Matrix Y Y ℂ) (hX : IsPositiveDefinite X)

/-- The frame `e_a = V β_a` of the dilation. -/
noncomputable def frame (a : Y ⊕ Y) : Space X hX := vec X hX (realBasis a)

theorem inner_frame (hone : X 1 = 1) (a b : Y ⊕ Y) :
    ⟪frame X hX a, frame X hX b⟫ = if a = b then 1 else 0 := by
  rw [frame, frame, inner_vec_vec, hone, re_pairing_one]

theorem inner_frame_mul_self (hone : X 1 = 1) (a b : Y ⊕ Y) :
    ⟪frame X hX a, frame X hX b⟫ * ⟪frame X hX a, frame X hX b⟫ = if a = b then 1 else 0 := by
  rw [inner_frame X hX hone]
  split_ifs <;> norm_num

theorem inner_frame_rep (g : G) (a b : Y ⊕ Y) :
    ⟪frame X hX a, rep X hX g (frame X hX b)⟫
      = (pairing (X g) (realBasis a) (realBasis b)).re :=
  inner_vec_rep_vec X hX _ _ g

/-- The almost invariant vector `η = (2k)^{-1/2} ∑ₐ e_a ⊗ e_a`. -/
noncomputable def eta : TensorSquare (Space X hX) :=
  (Real.sqrt (2 * (Fintype.card Y : ℝ)))⁻¹ • ∑ a, tmulC (frame X hX a) (frame X hX a)

/-- The moved vector `(A ⊗ 1) η`. -/
noncomputable def etaMoved (A : Space X hX ≃ₗᵢ[ℝ] Space X hX) : TensorSquare (Space X hX) :=
  (Real.sqrt (2 * (Fintype.card Y : ℝ)))⁻¹ • ∑ a, tmulC (A (frame X hX a)) (frame X hX a)

theorem inv_sqrt_mul_self {r : ℝ} (hr : 0 ≤ r) : (Real.sqrt r)⁻¹ * (Real.sqrt r)⁻¹ = r⁻¹ := by
  rw [← mul_inv, Real.mul_self_sqrt hr]

theorem sum_sum_ite_one : ∑ a : Y ⊕ Y, ∑ b : Y ⊕ Y, (if a = b then (1 : ℝ) else 0)
    = 2 * (Fintype.card Y : ℝ) := by
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_sum, nsmul_eq_mul, mul_one, Nat.cast_add]
  ring

theorem inner_eta_eta (hone : X 1 = 1) (hcard : 0 < Fintype.card Y) :
    ⟪eta X hX, eta X hX⟫ = 1 := by
  have hk : (0 : ℝ) < Fintype.card Y := Nat.cast_pos.mpr hcard
  rw [eta, real_inner_smul_left, real_inner_smul_right, inner_sum_tmulC]
  simp only [inner_frame_mul_self X hX hone]
  rw [sum_sum_ite_one, ← mul_assoc, inv_sqrt_mul_self (by positivity)]
  field_simp

theorem inner_etaMoved_self (hone : X 1 = 1) (hcard : 0 < Fintype.card Y)
    (A : Space X hX ≃ₗᵢ[ℝ] Space X hX) : ⟪etaMoved X hX A, etaMoved X hX A⟫ = 1 := by
  have hk : (0 : ℝ) < Fintype.card Y := Nat.cast_pos.mpr hcard
  rw [etaMoved, real_inner_smul_left, real_inner_smul_right, inner_sum_tmulC]
  simp only [LinearIsometryEquiv.inner_map_map, inner_frame_mul_self X hX hone]
  rw [sum_sum_ite_one, ← mul_assoc, inv_sqrt_mul_self (by positivity)]
  field_simp

theorem inner_diag_eta_eta (hcard : 0 < Fintype.card Y) (g : G) :
    ⟪diag (rep X hX) g (eta X hX), eta X hX⟫
      = (∑ x : Y, ∑ y : Y, ‖X g x y‖ ^ 2) / (Fintype.card Y : ℝ) := by
  have hk : (0 : ℝ) < Fintype.card Y := Nat.cast_pos.mpr hcard
  rw [eta, map_smul, map_sum, real_inner_smul_left, real_inner_smul_right]
  simp only [diag_tmulC]
  rw [inner_sum_tmulC]
  have h1 : ∀ a b : Y ⊕ Y, ⟪rep X hX g (frame X hX a), frame X hX b⟫
      * ⟪rep X hX g (frame X hX a), frame X hX b⟫
      = ((pairing (X g) (realBasis b) (realBasis a)).re) ^ 2 := by
    intro a b
    rw [real_inner_comm, inner_frame_rep, sq]
  simp only [h1]
  rw [Finset.sum_comm, sum_sq_re_pairing, ← mul_assoc, inv_sqrt_mul_self (by positivity)]
  field_simp

theorem inner_eta_etaMoved (hone : X 1 = 1) (hcard : 0 < Fintype.card Y)
    (A : Space X hX ≃ₗᵢ[ℝ] Space X hX) :
    ⟪eta X hX, etaMoved X hX A⟫
      = (∑ a, ⟪frame X hX a, A (frame X hX a)⟫) / (2 * (Fintype.card Y : ℝ)) := by
  have hk : (0 : ℝ) < Fintype.card Y := Nat.cast_pos.mpr hcard
  rw [eta, etaMoved, real_inner_smul_left, real_inner_smul_right, inner_sum_tmulC]
  simp only [inner_frame X hX hone, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  rw [← mul_assoc, inv_sqrt_mul_self (by positivity)]
  field_simp

end Frame

theorem re_normTrace (Y : FiniteModel) (A : Matrix Y Y ℂ) :
    (normTrace Y A).re = (Matrix.trace A).re / (Fintype.card Y : ℝ) := by
  have hc : ((Fintype.card Y : ℕ) : ℂ) = ((Fintype.card Y : ℝ) : ℂ) := by norm_cast
  rw [normTrace, hc, Complex.div_ofReal_re]

/-! ## Two estimates in an inner product space -/

theorem inner_lower_of_near {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (η ζ : E) (hη : ‖η‖ = 1) (hnear : ‖η - ζ‖ < 1 / 4) : 3 / 4 < ⟪ζ, η⟫ := by
  have h1 : ⟪ζ, η⟫ = ⟪η, η⟫ - ⟪η - ζ, η⟫ := by
    rw [inner_sub_left]
    ring
  have h2 := abs_real_inner_le_norm (η - ζ) η
  rw [hη, mul_one] at h2
  have h3 : ⟪η, η⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, hη]
    norm_num
  rw [h1, h3]
  have h4 := (abs_le.mp h2).2
  linarith

theorem inner_upper_of_near {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (η ζ w : E) (hw : ‖w‖ = 1) (hnear : ‖η - ζ‖ < 1 / 4) (hηw : ⟪η, w⟫ < 1 / 4) :
    ⟪ζ, w⟫ < 1 / 2 := by
  have h1 : ⟪ζ, w⟫ = ⟪η, w⟫ - ⟪η - ζ, w⟫ := by
    rw [inner_sub_left]
    ring
  have h2 := abs_real_inner_le_norm (η - ζ) w
  rw [hw, mul_one] at h2
  rw [h1]
  have h4 := (abs_le.mp h2).1
  linarith

/-! ## The contradiction for one positive definite matrix function -/

section Generic

variable {G : Type u} [Group G] {Y : Type} [Fintype Y] [DecidableEq Y]
variable (X : G → Matrix Y Y ℂ) (hX : IsPositiveDefinite X)

theorem norm_eta (hone : X 1 = 1) (hcard : 0 < Fintype.card Y) : ‖eta X hX‖ = 1 := by
  rw [norm_eq_sqrt_real_inner, inner_eta_eta X hX hone hcard, Real.sqrt_one]

theorem norm_etaMoved (hone : X 1 = 1) (hcard : 0 < Fintype.card Y)
    (A : Space X hX ≃ₗᵢ[ℝ] Space X hX) : ‖etaMoved X hX A‖ = 1 := by
  rw [norm_eq_sqrt_real_inner, inner_etaMoved_self X hX hone hcard A, Real.sqrt_one]

theorem norm_diag_eta_sub_lt (hone : X 1 = 1) (hcard : 0 < Fintype.card Y) {c : ℝ}
    (hc : 0 < c) (g : G)
    (hg : 1 - c ^ 2 / 2 < (∑ x : Y, ∑ y : Y, ‖X g x y‖ ^ 2) / (Fintype.card Y : ℝ)) :
    ‖diag (rep X hX) g (eta X hX) - eta X hX‖ < c := by
  have hsq : ‖diag (rep X hX) g (eta X hX) - eta X hX‖ ^ 2
      = 2 - 2 * ((∑ x : Y, ∑ y : Y, ‖X g x y‖ ^ 2) / (Fintype.card Y : ℝ)) := by
    rw [norm_sub_sq_real, LinearIsometryEquiv.norm_map, norm_eta X hX hone hcard,
      inner_diag_eta_eta X hX hcard g]
    ring
  have hlt : ‖diag (rep X hX) g (eta X hX) - eta X hX‖ ^ 2 < c ^ 2 := by
    rw [hsq]
    linarith
  exact lt_of_pow_lt_pow_left₀ 2 hc.le hlt

theorem inner_eta_etaMoved_rep (hone : X 1 = 1) (hcard : 0 < Fintype.card Y) (h : G) :
    ⟪eta X hX, etaMoved X hX (rep X hX h)⟫
      = (Matrix.trace (X h)).re / (Fintype.card Y : ℝ) := by
  rw [inner_eta_etaMoved X hX hone hcard]
  simp only [inner_frame_rep]
  rw [sum_re_pairing_diag, mul_div_mul_left _ _ (two_ne_zero : (2 : ℝ) ≠ 0)]

/-- **The contradiction step**: a nearly unitary positive definite matrix function with a
small trace at `h` makes `h` act nontrivially on a finite-dimensional subrepresentation of
the dilation. -/
theorem exists_moving_of_generic {Q : Finset G} {ε : ℝ} (hQ : IsKazhdanPair.{u, u} G Q ε)
    (hone : X 1 = 1) (hcard : 0 < Fintype.card Y) (h : G)
    (hgram : ∀ q ∈ Q,
      1 - ε ^ 2 / 32 < (∑ x : Y, ∑ y : Y, ‖X q x y‖ ^ 2) / (Fintype.card Y : ℝ))
    (htr : (Matrix.trace (X h)).re / (Fintype.card Y : ℝ) < 1 / 4) :
    ∃ W : Submodule ℝ (Space X hX), FiniteDimensional ℝ W ∧ IsInvariant (rep X hX) W ∧
      ∃ v ∈ W, rep X hX h v ≠ v := by
  have hε : 0 < ε := hQ.1
  have hmove : ∀ q ∈ Q, ‖diag (rep X hX) q (eta X hX) - eta X hX‖ < ε * (1 / 4) := by
    intro q hq
    refine norm_diag_eta_sub_lt X hX hone hcard (by positivity) q ?_
    have hc : (ε * (1 / 4)) ^ 2 / 2 = ε ^ 2 / 32 := by ring
    rw [hc]
    exact hgram q hq
  obtain ⟨ζ, hζinv, hζnear⟩ := KazhdanNearInvariantVector.exists_invariant_near hQ
    (diag (rep X hX)) (eta X hX) (by norm_num : (0 : ℝ) < 1 / 4) hmove
  by_contra hall
  push Not at hall
  have hid := inner_tmulC_of_forall_fixed (rep X hX) ζ hζinv h hall
  have hsame : ⟪ζ, etaMoved X hX (rep X hX h)⟫ = ⟪ζ, eta X hX⟫ := by
    rw [etaMoved, eta, real_inner_smul_right, real_inner_smul_right, inner_sum, inner_sum]
    simp only [hid]
  have hlow := inner_lower_of_near (eta X hX) ζ (norm_eta X hX hone hcard) hζnear
  have hηw : ⟪eta X hX, etaMoved X hX (rep X hX h)⟫ < 1 / 4 := by
    rw [inner_eta_etaMoved_rep X hX hone hcard h]
    exact htr
  have hhigh := inner_upper_of_near (eta X hX) ζ (etaMoved X hX (rep X hX h))
    (norm_etaMoved X hX hone hcard _) hζnear hηw
  linarith

end Generic

/-! ## The theorem -/

/-- **A nontrivial element acts nontrivially in a finite-dimensional orthogonal
representation**, for a Kazhdan group with the factorization property. -/
theorem exists_moving_representation (G : Type u) [Group G]
    (hT : HasKazhdanPropertyT.{u, u} G) (hfp : HasFactorizationProperty G) (h : G)
    (hh : h ≠ 1) :
    ∃ (W : Type u) (_ : NormedAddCommGroup W) (_ : InnerProductSpace ℝ W)
      (_ : FiniteDimensional ℝ W) (ρ : G →* (W ≃ₗᵢ[ℝ] W)), ρ h ≠ 1 := by
  classical
  obtain ⟨Q, ε, hQ⟩ := hT
  obtain ⟨M⟩ := hfp
  have hε : 0 < ε := hQ.1
  have hδpos : 0 < min (ε ^ 2 / 32) (1 / 4 : ℝ) := lt_min (by positivity) (by norm_num)
  obtain ⟨n, hcard, hgram, htr⟩ := KirchbergTraceModels.exists_index M Q hh hδpos
  have hX : IsPositiveDefinite (modelMatrix M n) :=
    ⟨fun g ↦ modelMatrix_conjTranspose M n g,
      fun m g w ↦ KirchbergTraceModels.modelMatrix_kernel_nonneg M n m g w⟩
  have hgram' : ∀ q ∈ Q, 1 - ε ^ 2 / 32
      < (∑ x, ∑ y, ‖modelMatrix M n q x y‖ ^ 2) / (Fintype.card (M.space n) : ℝ) := by
    intro q hq
    have h1 := (abs_lt.mp (hgram q hq)).1
    rw [re_normTrace, re_trace_conjTranspose_mul] at h1
    have h2 : min (ε ^ 2 / 32) (1 / 4 : ℝ) ≤ ε ^ 2 / 32 := min_le_left _ _
    linarith
  have htr' : (Matrix.trace (modelMatrix M n h)).re / (Fintype.card (M.space n) : ℝ)
      < 1 / 4 := by
    have h1 := (abs_lt.mp htr).2
    rw [re_normTrace] at h1
    have h2 : min (ε ^ 2 / 32) (1 / 4 : ℝ) ≤ 1 / 4 := min_le_right _ _
    linarith
  obtain ⟨W, hWfd, hWinv, v, hvW, hv⟩ := exists_moving_of_generic (modelMatrix M n) hX hQ
    (KirchbergTraceModels.modelMatrix_one M n) hcard h hgram' htr'
  refine ⟨W, inferInstance, inferInstance, hWfd,
    KazhdanFixedSpace.restrictToInvariantSubspace (rep (modelMatrix M n) hX) W hWinv, ?_⟩
  intro h1
  apply hv
  have h2 := congrArg
    (fun e : W ≃ₗᵢ[ℝ] W ↦ ((e ⟨v, hvW⟩ : W) : Space (modelMatrix M n) hX)) h1
  simpa using h2

/-- **Kirchberg's Theorem 1.1**, at the trace side of the factorization property:
the inhabitant of the typed input, with no assumption. -/
theorem kirchbergKazhdanFactorizationInput : KirchbergKazhdanFactorizationInput.{u} where
  residuallyFinite := fun G _ _ hT hfp ↦ by
    haveI : Group.FG G := KazhdanFiniteGeneration.fg_of_hasKazhdanPropertyT G hT
    exact OrthogonalRepresentationResiduallyFinite.isResiduallyFinite_of_forall_ne_one
      (fun x hx ↦ exists_moving_representation G hT hfp x hx)

/-- The printed theorem as a named proposition: a Kazhdan group with the
factorization property is residually finite.  No countability is needed. -/
def PrintedKirchbergTheorem : Prop :=
  ∀ (G : Type u) [Group G], HasKazhdanPropertyT.{u, u} G → HasFactorizationProperty G →
    IsResiduallyFinite G

theorem printedKirchbergTheorem : PrintedKirchbergTheorem.{u} := fun G _ hT hfp ↦ by
  haveI : Group.FG G := KazhdanFiniteGeneration.fg_of_hasKazhdanPropertyT G hT
  exact OrthogonalRepresentationResiduallyFinite.isResiduallyFinite_of_forall_ne_one
    (fun x hx ↦ exists_moving_representation G hT hfp x hx)

/-- **An infinite simple Kazhdan group lacks the factorization property**, with
Kirchberg's theorem proved. -/
theorem not_hasFactorizationProperty_of_simple_infinite_kazhdan (G : Type u) [Group G]
    [Countable G] [IsSimpleGroup G] [Infinite G] (hT : HasKazhdanPropertyT.{u, u} G) :
    ¬ HasFactorizationProperty G :=
  not_hasFactorizationProperty_of_isSimpleGroup_of_infinite_of_kazhdan
    kirchbergKazhdanFactorizationInput G hT

end KirchbergTheorem
end NinetyNineProblems
end GroupApproximation

open GroupApproximation.NinetyNineProblems.KirchbergTheorem

#audit_closed_axioms kirchbergKazhdanFactorizationInput
#audit_closed_axioms printedKirchbergTheorem
