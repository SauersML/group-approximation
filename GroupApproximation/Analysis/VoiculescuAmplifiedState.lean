import GroupApproximation.Analysis.VoiculescuAmplifiedRep

/-!
# (V3) The state Glimm's lemma is run on

The amplified representation of `Analysis/VoiculescuAmplifiedRep` carries the
state Voiculescu's argument feeds to Glimm's lemma: the vector state at the
diagonal vector `ζ = n^{-1/2}(e₁, …, eₙ)` of `K₀ⁿ`, whose value at a matrix
`[a_ij]` is `n⁻¹ Σ ⟪e_i, ρ(a_ij) e_j⟫`.  That is the functional whose
approximating vectors of `Hⁿ` become, read coordinatewise and rescaled, the tuple
the frame is built from.

## Why `n ≥ 1`

At `n = 0` the block space is zero, so `ζ = 0` and no unital state exists — `1 = 0`
in the zero algebra.  That is not a defect of the construction: at a zero
representation space the frame statement is satisfied by `T = 0`, since
`‖T⋆T - 1‖ = 0` when `1 = 0`.  The consumer splits on that case, and the
unitality of the state below carries `n ≠ 0`.

## Two constructions taken abstractly rather than at the block algebra

Both are performance, and both are the same lesson.

The factorisation of a nonnegative element inside a closed subalgebra is proved
at an abstract C⋆-algebra (`exists_mem_star_mul_self`) and instantiated.  Written
directly at `B(Hⁿ)` it does not elaborate: `IsSelfAdjoint (√S)` picks up the bare
`Star` instance of `E →L[ℂ] E` while `IsSelfAdjoint.of_nonneg` produces the one
projected out of `StarRing`, and reconciling them unfolds the whole `PiLp`
instance tower.  At an abstract algebra the two are the same variable.

The linear functional is assembled from `innerSL` and `ContinuousLinearMap.apply`
rather than proved linear by a tactic, for the same reason: additivity and
homogeneity are then structural, and nothing has to be unfolded.

## Positivity

The state's positivity is the one place where the subalgebra has to be closed.
A nonnegative element of `Mₙ(A)` is `y⋆y` with `y` again in `Mₙ(A)`, because the
continuous calculus does not leave a closed subalgebra; the value is then
`‖ρ⁽ⁿ⁾(y)ζ‖²`.  The square root is written through `CFC.sqrt_eq_real_sqrt`,
because `CFC.sqrt` is the `ℝ≥0`-calculus while the lemma that a functional
calculus stays inside a closed subalgebra is stated over an `RCLike` field.
-/

namespace GroupApproximation
namespace ShulmanFill

open scoped InnerProductSpace ComplexOrder

noncomputable section

/-! ## Factorisation inside a closed subalgebra -/

/-- **A nonnegative element of a closed star subalgebra factors inside it.**
Stated at an abstract C⋆-algebra: at `B(Hⁿ)` the same proof does not elaborate,
because the two paths to the `Star` instance have to be reconciled through the
`PiLp` tower. -/
theorem exists_mem_star_mul_self {B : Type} [CStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] [NonnegSpectrumClass ℝ B] (C : StarSubalgebra ℂ B)
    [IsClosed (C : Set B)] {x : B} (hxC : x ∈ C) (hx : 0 ≤ x) :
    ∃ y ∈ C, star y * y = x := by
  refine ⟨CFC.sqrt x, ?_, ?_⟩
  · rw [CFC.sqrt_eq_real_sqrt x hx]
    exact cfcₙ_mem (𝕜 := ℝ) (𝕜' := ℂ) Real.sqrt hxC
  · rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg x)).star_eq,
      CFC.sqrt_mul_sqrt_self x hx]

/-- **The vector state of a represented square is a squared norm.**
Proved before specializing to block spaces so that the star and adjoint
instances are reconciled at abstract type variables rather than through the
`PiLp` instance tower. -/
theorem inner_starAlgHom_star_mul_self_eq_norm_sq
    {B E : Type} [CStarAlgebra B] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (pi : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (y : B) (zeta : E) :
    ⟪zeta, pi (star y * y) zeta⟫_ℂ = ((‖pi y zeta‖ ^ 2 : ℝ) : ℂ) := by
  rw [map_mul, map_star, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  norm_cast

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
  {K₀ : Type} [NormedAddCommGroup K₀] [InnerProductSpace ℂ K₀]
  [CompleteSpace K₀]
  {n : ℕ} {A : StarSubalgebra ℂ (H →L[ℂ] H)}

/-! ## The diagonal vector -/

variable (K₀) in
/-- The diagonal vector `n^{-1/2}(e₁, …, eₙ)` of `K₀ⁿ`. -/
def diagVector (b : OrthonormalBasis (Fin n) ℂ K₀) : BlockSpace K₀ n :=
  ∑ i : Fin n, (((Real.sqrt n)⁻¹ : ℝ) : ℂ) • hBlockIncl K₀ n i (b i)

theorem diagVector_coord (b : OrthonormalBasis (Fin n) ℂ K₀) (r : Fin n) :
    hBlockProj K₀ n r (diagVector K₀ b) = (((Real.sqrt n)⁻¹ : ℝ) : ℂ) • b r := by
  rw [diagVector, map_sum]
  rw [Finset.sum_eq_single r]
  · rw [map_smul]
    congr 1
    exact hBlockIncl_coord_same r (b r)
  · intro i _ hi
    rw [map_smul,
      show hBlockProj K₀ n r (hBlockIncl K₀ n i (b i)) = 0 from
        hBlockIncl_coord_ne (Ne.symm hi) (b i), smul_zero]
  · intro h
    exact absurd (Finset.mem_univ r) h

theorem inner_diagVector_self (hn : n ≠ 0) (b : OrthonormalBasis (Fin n) ℂ K₀) :
    ⟪diagVector K₀ b, diagVector K₀ b⟫_ℂ = 1 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hsq : ((Real.sqrt n)⁻¹ : ℝ) * ((Real.sqrt n)⁻¹ : ℝ) = (n : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hnpos.le]
  have hcast : (((n : ℝ)⁻¹ : ℝ) : ℂ) = ((n : ℂ))⁻¹ := by push_cast; ring
  rw [inner_block_eq_sum]
  have hterm : ∀ r : Fin n,
      ⟪diagVector K₀ b r, diagVector K₀ b r⟫_ℂ = ((n : ℂ))⁻¹ := by
    intro r
    have hbb : ⟪b r, b r⟫_ℂ = 1 := by simp
    have hc : diagVector K₀ b r = (((Real.sqrt n)⁻¹ : ℝ) : ℂ) • b r :=
      diagVector_coord b r
    rw [hc, inner_smul_left, inner_smul_right, hbb]
    simp only [Complex.conj_ofReal, mul_one]
    rw [← Complex.ofReal_mul, hsq, hcast]
  rw [Finset.sum_congr rfl fun r _ ↦ hterm r, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hn)

/-! ## The state -/

variable (A) in
/-- The vector state of the amplified representation at the diagonal vector, as
a linear functional.  Assembled from `innerSL` and evaluation so that linearity
is structural. -/
def ampStateLin (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ K₀)
    (rho : ↥A →⋆ₐ[ℂ] (K₀ →L[ℂ] K₀)) : ↥(ampSubalgebra A n) →ₗ[ℂ] ℂ :=
  (((innerSL ℂ (diagVector K₀ b)).comp
      (ContinuousLinearMap.apply ℂ (BlockSpace K₀ n)
        (diagVector K₀ b))).toLinearMap).comp
    (ampRep A n rho).toAlgHom.toLinearMap

variable (A) in
@[simp] theorem ampStateLin_apply (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ K₀)
    (rho : ↥A →⋆ₐ[ℂ] (K₀ →L[ℂ] K₀)) (S : ↥(ampSubalgebra A n)) :
    ampStateLin A n b rho S
      = ⟪diagVector K₀ b, ampRep A n rho S (diagVector K₀ b)⟫_ℂ := rfl

/-- **The state is nonnegative on nonnegative elements.** -/
theorem ampStateLin_nonneg (hA : IsClosed (A : Set (H →L[ℂ] H))) (n : ℕ)
    (b : OrthonormalBasis (Fin n) ℂ K₀) (rho : ↥A →⋆ₐ[ℂ] (K₀ →L[ℂ] K₀))
    (S : ↥(ampSubalgebra A n)) (hS : 0 ≤ S) :
    ∃ r : ℝ, 0 ≤ r ∧ ampStateLin A n b rho S = r := by
  haveI : IsClosed ((ampSubalgebra A n :
    Set (BlockSpace H n →L[ℂ] BlockSpace H n))) := isClosed_ampSubalgebra A n hA
  have hSnn : (0 : BlockSpace H n →L[ℂ] BlockSpace H n)
      ≤ (S : BlockSpace H n →L[ℂ] BlockSpace H n) := hS
  obtain ⟨y, hyC, hy⟩ := exists_mem_star_mul_self (ampSubalgebra A n) S.2 hSnn
  have hfact : star (⟨y, hyC⟩ : ↥(ampSubalgebra A n)) * ⟨y, hyC⟩ = S :=
    Subtype.ext hy
  refine ⟨‖ampRep A n rho ⟨y, hyC⟩ (diagVector K₀ b)‖ ^ 2, by positivity, ?_⟩
  rw [ampStateLin_apply, ← hfact]
  exact inner_starAlgHom_star_mul_self_eq_norm_sq
    (ampRep A n rho) ⟨y, hyC⟩ (diagVector K₀ b)

variable (A) in
/-- **The state Glimm's lemma is run on.** -/
def ampState (hA : IsClosed (A : Set (H →L[ℂ] H))) (n : ℕ)
    (b : OrthonormalBasis (Fin n) ℂ K₀) (rho : ↥A →⋆ₐ[ℂ] (K₀ →L[ℂ] K₀)) :
    ↥(ampSubalgebra A n) →ₚ[ℂ] ℂ where
  toLinearMap := ampStateLin A n b rho
  monotone' := by
    intro S T hST
    obtain ⟨r, hr0, hr⟩ :=
      ampStateLin_nonneg hA n b rho (T - S) (sub_nonneg.mpr hST)
    rw [map_sub] at hr
    have hre := congrArg Complex.re hr
    have him := congrArg Complex.im hr
    rw [Complex.sub_re, Complex.ofReal_re] at hre
    rw [Complex.sub_im, Complex.ofReal_im] at him
    show ampStateLin A n b rho S ≤ ampStateLin A n b rho T
    rw [Complex.le_def]
    refine ⟨by linarith, by linarith⟩

variable (A) in
@[simp] theorem ampState_apply (hA : IsClosed (A : Set (H →L[ℂ] H))) (n : ℕ)
    (b : OrthonormalBasis (Fin n) ℂ K₀) (rho : ↥A →⋆ₐ[ℂ] (K₀ →L[ℂ] K₀))
    (S : ↥(ampSubalgebra A n)) :
    ampState A hA n b rho S
      = ⟪diagVector K₀ b, ampRep A n rho S (diagVector K₀ b)⟫_ℂ := rfl

theorem ampState_one (hA : IsClosed (A : Set (H →L[ℂ] H))) (hn : n ≠ 0)
    (b : OrthonormalBasis (Fin n) ℂ K₀) (rho : ↥A →⋆ₐ[ℂ] (K₀ →L[ℂ] K₀)) :
    ampState A hA n b rho 1 = 1 := by
  rw [ampState_apply, map_one]
  exact inner_diagVector_self hn b

end

end ShulmanFill
end GroupApproximation
