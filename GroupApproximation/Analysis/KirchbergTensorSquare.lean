import GroupApproximation.Analysis.KirchbergCompletionRepresentation
import GroupApproximation.Analysis.KirchbergCompactExtraction
import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# The completed tensor square and its slice operators

For a real Hilbert space `K`, `TensorSquare K` is the completion of `K ⊗[ℝ] K`.
An orthogonal representation `σ` of `G` on `K` gives the diagonal representation
`σ ⊗ σ` on it (`diag`).

When `K` is complete, every `ζ ∈ K ⊗̂ K` defines the slice operator
`slice ζ : K →L K` by `⟪slice ζ y, x⟫ = ⟪ζ, x ⊗ y⟫`.  It is compact: algebraic
tensors give finite-rank slices, `‖slice ζ‖ ≤ ‖ζ‖`, and compact operators are
closed.  If `ζ` is diagonally invariant, `slice ζ` commutes with `σ`.

Through `KirchbergCompactExtraction.apply_eq_of_forall_finiteDimensional_fixed`:
if `h` fixes every finite-dimensional invariant subspace pointwise, then
`⟪ζ, σ(h)x ⊗ y⟫ = ⟪ζ, x ⊗ y⟫` for all `x, y` (`inner_tmulC_of_forall_fixed`).
That identity is the contradiction step of Kirchberg's Theorem 1.1.
-/

namespace GroupApproximation
namespace KirchbergTensorSquare

open UniformSpace TensorProduct KirchbergCompactExtraction

universe u v

variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℝ K]

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- The completed real tensor square `K ⊗̂ K`. -/
abbrev TensorSquare (K : Type v) [NormedAddCommGroup K] [InnerProductSpace ℝ K] :=
  Completion (K ⊗[ℝ] K)

/-- The elementary tensor `x ⊗ y` in the completed tensor square. -/
noncomputable def tmulC (x y : K) : TensorSquare K := ((x ⊗ₜ[ℝ] y : K ⊗[ℝ] K) : Completion _)

theorem inner_tmulC (a b c d : K) : ⟪tmulC a b, tmulC c d⟫ = ⟪a, c⟫ * ⟪b, d⟫ := by
  rw [tmulC, tmulC, Completion.inner_coe, TensorProduct.inner_tmul]

theorem norm_tmulC (x y : K) : ‖tmulC x y‖ = ‖x‖ * ‖y‖ := by
  rw [tmulC, Completion.norm_coe, TensorProduct.norm_tmul]

theorem tmulC_add_left (x x' y : K) : tmulC (x + x') y = tmulC x y + tmulC x' y := by
  rw [tmulC, tmulC, tmulC, TensorProduct.add_tmul, Completion.coe_add]

theorem tmulC_add_right (x y y' : K) : tmulC x (y + y') = tmulC x y + tmulC x y' := by
  rw [tmulC, tmulC, tmulC, TensorProduct.tmul_add, Completion.coe_add]

theorem tmulC_smul_left (r : ℝ) (x y : K) : tmulC (r • x) y = r • tmulC x y := by
  rw [tmulC, tmulC, ← TensorProduct.smul_tmul', Completion.coe_smul]

theorem tmulC_smul_right (r : ℝ) (x y : K) : tmulC x (r • y) = r • tmulC x y := by
  rw [tmulC, tmulC, TensorProduct.tmul_smul, Completion.coe_smul]

theorem inner_sum_tmulC {ι : Type*} [Fintype ι] (u v w z : ι → K) :
    ⟪∑ a, tmulC (u a) (v a), ∑ b, tmulC (w b) (z b)⟫ = ∑ a, ∑ b, ⟪u a, w b⟫ * ⟪v a, z b⟫ := by
  simp only [sum_inner, inner_sum, inner_tmulC]
  exact Finset.sum_comm

/-! ## The diagonal representation -/

variable {G : Type u} [Group G]

/-- The diagonal representation on the algebraic tensor square. -/
noncomputable def diagPre (σ : G →* (K ≃ₗᵢ[ℝ] K)) : G →* (K ⊗[ℝ] K ≃ₗᵢ[ℝ] K ⊗[ℝ] K) where
  toFun g := TensorProduct.congrIsometry (σ g) (σ g)
  map_one' := LinearIsometryEquiv.ext fun t ↦ by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      show (σ 1) a ⊗ₜ[ℝ] (σ 1) b = a ⊗ₜ[ℝ] b
      simp only [map_one, LinearIsometryEquiv.coe_one, id_eq]
    | add a b ha hb => rw [map_add, ha, hb, map_add]
  map_mul' g h := LinearIsometryEquiv.ext fun t ↦ by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      show (σ (g * h)) a ⊗ₜ[ℝ] (σ (g * h)) b = (σ g) ((σ h) a) ⊗ₜ[ℝ] (σ g) ((σ h) b)
      simp only [map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply]
    | add a b ha hb => rw [map_add, ha, hb, map_add]

/-- **The diagonal representation `σ ⊗ σ` on the completed tensor square.** -/
noncomputable def diag (σ : G →* (K ≃ₗᵢ[ℝ] K)) :
    G →* (TensorSquare K ≃ₗᵢ[ℝ] TensorSquare K) :=
  KirchbergCompletion.completionRep (diagPre σ)

theorem diag_tmulC (σ : G →* (K ≃ₗᵢ[ℝ] K)) (g : G) (a b : K) :
    diag σ g (tmulC a b) = tmulC (σ g a) (σ g b) := by
  rw [diag, tmulC, KirchbergCompletion.completionRep_coe, tmulC]
  congr 1

/-! ## Slice operators -/

/-- The functional `x ↦ ⟪ζ, x ⊗ y⟫`. -/
noncomputable def sliceFunctional (ζ : TensorSquare K) (y : K) : StrongDual ℝ K :=
  LinearMap.mkContinuous
    { toFun := fun x ↦ ⟪ζ, tmulC x y⟫
      map_add' := fun x x' ↦ by rw [tmulC_add_left, inner_add_right]
      map_smul' := fun r x ↦ by
        rw [tmulC_smul_left, real_inner_smul_right, RingHom.id_apply, smul_eq_mul] }
    (‖ζ‖ * ‖y‖) (fun x ↦ by
      rw [Real.norm_eq_abs]
      calc |⟪ζ, tmulC x y⟫| ≤ ‖ζ‖ * ‖tmulC x y‖ := abs_real_inner_le_norm _ _
        _ = ‖ζ‖ * ‖y‖ * ‖x‖ := by rw [norm_tmulC]; ring)

theorem sliceFunctional_apply (ζ : TensorSquare K) (y x : K) :
    sliceFunctional ζ y x = ⟪ζ, tmulC x y⟫ := rfl

variable [CompleteSpace K]

/-- The slice of `ζ` at `y`. -/
noncomputable def sliceFun (ζ : TensorSquare K) (y : K) : K :=
  (InnerProductSpace.toDual ℝ K).symm (sliceFunctional ζ y)

theorem inner_sliceFun (ζ : TensorSquare K) (y x : K) :
    ⟪sliceFun ζ y, x⟫ = ⟪ζ, tmulC x y⟫ := by
  rw [sliceFun, InnerProductSpace.toDual_symm_apply, sliceFunctional_apply]

theorem norm_sliceFun_le (ζ : TensorSquare K) (y : K) : ‖sliceFun ζ y‖ ≤ ‖ζ‖ * ‖y‖ := by
  set z := sliceFun ζ y with hz
  have h1 : ‖z‖ ^ 2 = ⟪ζ, tmulC z y⟫ := by
    rw [← real_inner_self_eq_norm_sq, hz, inner_sliceFun]
  have h2 : ⟪ζ, tmulC z y⟫ ≤ ‖ζ‖ * (‖z‖ * ‖y‖) := by
    have := real_inner_le_norm ζ (tmulC z y)
    rwa [norm_tmulC] at this
  by_cases hz0 : ‖z‖ = 0
  · rw [hz0]
    positivity
  · have hzpos : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz0)
    refine le_of_mul_le_mul_left ?_ hzpos
    nlinarith

/-- **The slice operator** `⟪slice ζ y, x⟫ = ⟪ζ, x ⊗ y⟫`. -/
noncomputable def slice (ζ : TensorSquare K) : K →L[ℝ] K :=
  LinearMap.mkContinuous
    { toFun := sliceFun ζ
      map_add' := fun y y' ↦ ext_inner_right ℝ fun x ↦ by
        rw [inner_add_left, inner_sliceFun, inner_sliceFun, inner_sliceFun, tmulC_add_right,
          inner_add_right]
      map_smul' := fun r y ↦ ext_inner_right ℝ fun x ↦ by
        rw [RingHom.id_apply, real_inner_smul_left, inner_sliceFun, inner_sliceFun,
          tmulC_smul_right, real_inner_smul_right] }
    ‖ζ‖ (norm_sliceFun_le ζ)

theorem inner_slice (ζ : TensorSquare K) (y x : K) : ⟪slice ζ y, x⟫ = ⟪ζ, tmulC x y⟫ :=
  inner_sliceFun ζ y x

theorem norm_slice_le (ζ : TensorSquare K) : ‖slice ζ‖ ≤ ‖ζ‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg ζ) _

theorem slice_add (ζ ζ' : TensorSquare K) : slice (ζ + ζ') = slice ζ + slice ζ' :=
  ContinuousLinearMap.ext fun y ↦ ext_inner_right ℝ fun x ↦ by
    change ⟪slice (ζ + ζ') y, x⟫ = ⟪slice ζ y + slice ζ' y, x⟫
    rw [inner_add_left, inner_slice, inner_slice, inner_slice, inner_add_left]

theorem slice_smul (r : ℝ) (ζ : TensorSquare K) : slice (r • ζ) = r • slice ζ :=
  ContinuousLinearMap.ext fun y ↦ ext_inner_right ℝ fun x ↦ by
    change ⟪slice (r • ζ) y, x⟫ = ⟪r • slice ζ y, x⟫
    rw [real_inner_smul_left, inner_slice, inner_slice, real_inner_smul_left]

theorem slice_zero : slice (0 : TensorSquare K) = 0 :=
  ContinuousLinearMap.ext fun y ↦ ext_inner_right ℝ fun x ↦ by
    change ⟪slice 0 y, x⟫ = ⟪(0 : K), x⟫
    rw [inner_slice, inner_zero_left, inner_zero_left]

/-- The slice map as a continuous linear map. -/
noncomputable def sliceL : TensorSquare K →L[ℝ] (K →L[ℝ] K) :=
  LinearMap.mkContinuous
    { toFun := slice
      map_add' := slice_add
      map_smul' := slice_smul }
    1 (fun ζ ↦ by rw [one_mul]; exact norm_slice_le ζ)

theorem slice_tmulC (a b y : K) : slice (tmulC a b) y = ⟪b, y⟫ • a :=
  ext_inner_right ℝ fun x ↦ by
    rw [inner_slice, inner_tmulC, real_inner_smul_left, mul_comm]

theorem slice_coe_finiteRank (t : K ⊗[ℝ] K) :
    ∃ W : Submodule ℝ K, FiniteDimensional ℝ W ∧ ∀ y, slice (t : TensorSquare K) y ∈ W := by
  induction t using TensorProduct.induction_on with
  | zero =>
    refine ⟨⊥, inferInstance, fun y ↦ ?_⟩
    have h0 : ((0 : K ⊗[ℝ] K) : TensorSquare K) = 0 := Completion.coe_zero
    rw [h0, slice_zero]
    exact Submodule.zero_mem _
  | tmul a b =>
    refine ⟨ℝ ∙ a, inferInstance, fun y ↦ ?_⟩
    change slice (tmulC a b) y ∈ ℝ ∙ a
    rw [slice_tmulC]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a)
  | add t t' ht ht' =>
    obtain ⟨W, hW, hy⟩ := ht
    obtain ⟨W', hW', hy'⟩ := ht'
    haveI := hW
    haveI := hW'
    refine ⟨W ⊔ W', inferInstance, fun y ↦ ?_⟩
    rw [Completion.coe_add, slice_add]
    change slice (t : TensorSquare K) y + slice (t' : TensorSquare K) y ∈ W ⊔ W'
    exact Submodule.add_mem _ (Submodule.mem_sup_left (hy y)) (Submodule.mem_sup_right (hy' y))

/-- **Slice operators are compact.** -/
theorem isCompactOperator_slice (ζ : TensorSquare K) : IsCompactOperator (slice ζ) := by
  have hclosed : IsClosed {ζ : TensorSquare K | IsCompactOperator (slice ζ)} :=
    IsClosed.preimage (sliceL (K := K)).continuous isClosed_setOf_isCompactOperator
  induction ζ using Completion.induction_on with
  | hp => exact hclosed
  | ih t =>
    obtain ⟨W, hW, hy⟩ := slice_coe_finiteRank t
    haveI := hW
    have h := isCompactOperator_of_locallyCompactSpace_dom
      ((slice (t : TensorSquare K)).codRestrict W hy)
    exact h.clm_comp W.subtypeL

/-- **An invariant vector gives an intertwining slice.** -/
theorem slice_comm_of_invariant (σ : G →* (K ≃ₗᵢ[ℝ] K)) (ζ : TensorSquare K)
    (hζ : ∀ g : G, diag σ g ζ = ζ) (g : G) (y : K) :
    slice ζ (σ g y) = σ g (slice ζ y) := by
  refine ext_inner_right ℝ fun x ↦ ?_
  have hcancel : σ g (σ g⁻¹ x) = x := by simp
  calc ⟪slice ζ (σ g y), x⟫ = ⟪ζ, tmulC x (σ g y)⟫ := inner_slice ζ (σ g y) x
    _ = ⟪diag σ g ζ, diag σ g (tmulC (σ g⁻¹ x) y)⟫ := by rw [hζ, diag_tmulC, hcancel]
    _ = ⟪ζ, tmulC (σ g⁻¹ x) y⟫ := (diag σ g).inner_map_map _ _
    _ = ⟪slice ζ y, σ g⁻¹ x⟫ := (inner_slice ζ y _).symm
    _ = ⟪σ g (slice ζ y), σ g (σ g⁻¹ x)⟫ := ((σ g).inner_map_map _ _).symm
    _ = ⟪σ g (slice ζ y), x⟫ := by rw [hcancel]

theorem inner_tmulC_of_fixed (σ : G →* (K ≃ₗᵢ[ℝ] K)) (ζ : TensorSquare K) (h : G)
    (hfix : ∀ y, σ h (slice ζ y) = slice ζ y) (x y : K) :
    ⟪ζ, tmulC (σ h x) y⟫ = ⟪ζ, tmulC x y⟫ :=
  calc ⟪ζ, tmulC (σ h x) y⟫ = ⟪slice ζ y, σ h x⟫ := (inner_slice ζ y _).symm
    _ = ⟪σ h (slice ζ y), σ h x⟫ := by rw [hfix y]
    _ = ⟪slice ζ y, x⟫ := (σ h).inner_map_map _ _
    _ = ⟪ζ, tmulC x y⟫ := inner_slice ζ y x

/-- **The contradiction identity of Kirchberg's Theorem 1.1.**  If `ζ` is
diagonally invariant and `h` fixes every finite-dimensional invariant subspace
pointwise, then `⟪ζ, σ(h)x ⊗ y⟫ = ⟪ζ, x ⊗ y⟫`. -/
theorem inner_tmulC_of_forall_fixed (σ : G →* (K ≃ₗᵢ[ℝ] K)) (ζ : TensorSquare K)
    (hζ : ∀ g : G, diag σ g ζ = ζ) (h : G)
    (hfd : ∀ W : Submodule ℝ K, FiniteDimensional ℝ W → IsInvariant σ W →
      ∀ v ∈ W, σ h v = v) (x y : K) :
    ⟪ζ, tmulC (σ h x) y⟫ = ⟪ζ, tmulC x y⟫ :=
  inner_tmulC_of_fixed σ ζ h
    (fun y ↦ apply_eq_of_forall_finiteDimensional_fixed σ (slice ζ) (isCompactOperator_slice ζ)
      (slice_comm_of_invariant σ ζ hζ) h hfd y) x y

end KirchbergTensorSquare
end GroupApproximation
