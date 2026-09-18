import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.EmbeddingConnesDefs

/-!
# Connes' trick: compressions of ucp maps are completely positive

Lane TWWSch3b1 (WO-TWWSch-3b-1), toward `isAmenableTrace_of_isNuclearCStarAlgebra`
(`non_mf_group_notes.tex`, Tikuisis--White--Winter input to Schafhauser's argument). Source:
Brown--Ozawa, *C⋆-algebras and finite-dimensional approximations*, Thm 6.2.7 (Connes' trick).
Adapted from the never-wired foreign `TWWLanes/ConnesTrick` module of the same content.

Connes' trick (Brown--Ozawa, Thm 6.2.7) builds new matrix models out of an old model
`φ : A → M_Y` by compressing:

* `x ↦ Vᴴ φ(x) V` for a rectangular `V : Matrix Y Z ℂ`, which is used to diagonalise the
  density;
* `x ↦ ∑ₖ (Vₖ)ᴴ φ(x) Vₖ`, which is used to assemble the spectral layers.

This file proves that complete positivity in the corpus "form sense"
(`Quasidiagonal.IsCompletelyPositiveOnMatrices`) passes to both. The form of the compressed
map at the vectors `wᵢ` is the form of `φ` at the vectors `V wᵢ`. With several `Vₖ`, the form
is a sum of such forms, and a sum of real nonnegative numbers is real and nonnegative.

It also packages `x ↦ Vᴴ x V` as a `ℂ`-linear map, `conjLinear V`, so that `conjLinear V ∘ₗ φ`
is again a linear map into matrices. Everything here is proved.
-/

namespace GroupApproximation.Full.TWWSchafhauser.Connes

open Matrix Quasidiagonal

noncomputable section

universe u

variable {A : Type u} [CStarAlgebra A]

/-- The sesquilinear form of `M` at `(u, v)`, written as a dot product. -/
theorem form_eq_dotProduct {m : Type*} [Fintype m] (M : Matrix m m ℂ) (u v : m → ℂ) :
    ∑ x : m, ∑ y : m, (starRingEnd ℂ) (u x) * M x y * v y = star u ⬝ᵥ (M *ᵥ v) := by
  first
    | (simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, starRingEnd_apply,
        mul_assoc]; done)
    | simp [dotProduct, mulVec, Finset.mul_sum, mul_assoc]

/-- The form of the compression `Vᴴ M V` at `(u, v)` is the form of `M` at `(V u, V v)`. -/
theorem dotProduct_conjTranspose_mul_mul_mulVec {m n : Type*} [Fintype m] [Fintype n]
    (V : Matrix m n ℂ) (M : Matrix m m ℂ) (u v : n → ℂ) :
    star u ⬝ᵥ ((Vᴴ * M * V) *ᵥ v) = star (V *ᵥ u) ⬝ᵥ (M *ᵥ (V *ᵥ v)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.star_mulVec]

/-- Moves the innermost of three finite sums to the outside. -/
theorem sum_sum_sum_comm {α β γ M : Type*} [AddCommMonoid M] [Fintype α] [Fintype β]
    [Fintype γ] (f : α → β → γ → M) :
    ∑ a, ∑ b, ∑ c, f a b c = ∑ c, ∑ a, ∑ b, f a b c := by
  calc ∑ a, ∑ b, ∑ c, f a b c = ∑ a, ∑ c, ∑ b, f a b c :=
        Finset.sum_congr rfl fun a _ ↦ Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, f a b c := Finset.sum_comm

/-- The form of a sum of compressions is the sum of the compressed forms. -/
theorem form_sum_conj {ι : Type*} [Fintype ι] {m n : Type*} [Fintype m] [Fintype n]
    (V : ι → Matrix m n ℂ) (M : Matrix m m ℂ) (u v : n → ℂ) :
    ∑ x : n, ∑ y : n, (starRingEnd ℂ) (u x) * (∑ k, (V k)ᴴ * M * V k) x y * v y
      = ∑ k, ∑ x : m, ∑ y : m,
        (starRingEnd ℂ) ((V k *ᵥ u) x) * M x y * (V k *ᵥ v) y := by
  rw [form_eq_dotProduct (∑ k, (V k)ᴴ * M * V k) u v, Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [form_eq_dotProduct M (V k *ᵥ u) (V k *ᵥ v), dotProduct_conjTranspose_mul_mul_mulVec]

/-- **A sum of compressions of a completely positive map is completely positive.** -/
theorem isCompletelyPositiveOnMatrices_sum_conj {ι : Type*} [Fintype ι] (Y Z : FiniteModel)
    (φ : A → Matrix Y Y ℂ) (hφ : IsCompletelyPositiveOnMatrices Y φ)
    (V : ι → Matrix Y Z ℂ) :
    IsCompletelyPositiveOnMatrices Z (fun x ↦ ∑ k, (V k)ᴴ * φ x * V k) := by
  intro m a w
  have hk := fun k : ι ↦ hφ m a fun i ↦ V k *ᵥ w i
  simp only [form_sum_conj]
  rw [sum_sum_sum_comm, Complex.im_sum, Complex.re_sum]
  exact ⟨Finset.sum_eq_zero fun k _ ↦ (hk k).1, Finset.sum_nonneg fun k _ ↦ (hk k).2⟩

/-- **A compression of a completely positive map is completely positive.** -/
theorem isCompletelyPositiveOnMatrices_conj (Y Z : FiniteModel) (φ : A → Matrix Y Y ℂ)
    (hφ : IsCompletelyPositiveOnMatrices Y φ) (V : Matrix Y Z ℂ) :
    IsCompletelyPositiveOnMatrices Z (fun x ↦ Vᴴ * φ x * V) := by
  have h := isCompletelyPositiveOnMatrices_sum_conj Y Z φ hφ (fun _ : Unit ↦ V)
  first
    | simpa only [Fintype.sum_unique] using h
    | simpa using h

/-- Compression `M ↦ Vᴴ M V`, as a `ℂ`-linear map between matrix algebras. -/
def conjLinear {m n : Type*} [Fintype m] [Fintype n] (V : Matrix m n ℂ) :
    Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ where
  toFun M := Vᴴ * M * V
  map_add' M N := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' c M := by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

theorem conjLinear_apply {m n : Type*} [Fintype m] [Fintype n] (V : Matrix m n ℂ)
    (M : Matrix m m ℂ) : conjLinear V M = Vᴴ * M * V := rfl

/-- A compression by an isometry (`Vᴴ V = 1`) is unital. -/
theorem conjLinear_one {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (V : Matrix m n ℂ) (hV : Vᴴ * V = 1) : conjLinear V 1 = 1 := by
  rw [conjLinear_apply, Matrix.mul_one, hV]

/-- The compression of a ucp model by an isometry is a ucp model. -/
theorem ucp_conjLinear_comp (Y Z : FiniteModel) (φ : A →ₗ[ℂ] Matrix Y Y ℂ)
    (hone : φ 1 = 1) (hφ : IsCompletelyPositiveOnMatrices Y ⇑φ) (V : Matrix Y Z ℂ)
    (hV : Vᴴ * V = 1) :
    (conjLinear V ∘ₗ φ) 1 = 1 ∧ IsCompletelyPositiveOnMatrices Z ⇑(conjLinear V ∘ₗ φ) := by
  refine ⟨?_, ?_⟩
  · rw [LinearMap.comp_apply, hone, conjLinear_one V hV]
  · have h := isCompletelyPositiveOnMatrices_conj Y Z (⇑φ) hφ V
    first
      | exact h
      | exact fun m a w ↦ h m a w

end

end GroupApproximation.Full.TWWSchafhauser.Connes
