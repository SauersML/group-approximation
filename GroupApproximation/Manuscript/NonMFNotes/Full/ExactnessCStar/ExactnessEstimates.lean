import GroupApproximation.Manuscript.NonMFNotes.Full.ExactnessCStar.SchurMultiplier
import GroupApproximation.Manuscript.NonMFNotes.Full.ExactnessCStar.CompressionContractive
import GroupApproximation.Analysis.CStarIdealApproximateUnit

/-!
# The tensor estimates of the property-A exactness argument

Source: `non_mf_group_notes.tex`, section `sec:Esofic`, paragraph
"Exactness", last sentence: for a discrete group, group exactness gives
exactness of the reduced group C⋆-algebra \cite{KWExact}.  With
`J : C*_r(G) → B(ℓ²(G))` the inclusion and `Φ` the Schur multiplier of a
property-A witness, the Kirchberg--Wassermann / Ozawa argument splits
`id ⊗ J = (id ⊗ (J - Φ)) + (id ⊗ Φ)` on `B ⊗ C*_r(G)` and estimates the two
pieces separately:

* `minTensorNorm_lTensor_regInclusion` --- `id ⊗ J` is isometric;
* `minTensorNorm_lTensor_schurMultiplier_le` --- `id ⊗ Φ` is contractive;
* `minTensorNorm_lTensor_schurDefect_le` --- `‖id ⊗ (J - Φ)‖ ≤ 2`;
* `norm_minTensorIn_lTensor_schurDefect_translationForm_le` --- on a
  translation form supported in `R`, `id ⊗ (J - Φ)` costs at most
  `(∑ ‖f g‖) ε / 2`;
* `lTensor_schurMultiplier_translationForm` --- `id ⊗ Φ` only sees the
  finite difference set of the witness;
* `norm_lTensor_regInclusion_mul_le`, `norm_lTensor_schurMultiplier_mul_le`,
  `norm_lTensor_schurDefect_le_of_near` --- the three estimates consumed by the
  assembly;
* `minTensorIn_mul_tmul_one_mem` and `exists_approxUnit_absorb` --- the ideal
  side: right multiplication by `e ⊗ 1` with `e ∈ I` lands in `I ⊙ C`, and an
  approximate unit absorbs finitely many ideal elements at once.
-/

namespace GroupApproximation.Full.NN09c

open GroupApproximation.CStarTensor GroupApproximation.ExactnessPermanence
open GroupApproximation.ReducedGroupCStarTrace
open scoped TensorProduct

universe u v

noncomputable section

section Operators

variable (G : Type u) [Group G]

/-- `B(ℓ²(G))` is nontrivial: it contains the nontrivial algebra `C*_r(G)`. -/
theorem nontrivial_groupOperators : Nontrivial (GroupHilbert G →L[ℂ] GroupHilbert G) :=
  Function.Injective.nontrivial
    (f := fun c : ReducedGroupCStar G ↦ (c : GroupHilbert G →L[ℂ] GroupHilbert G))
    Subtype.val_injective

/-- The inclusion `J : C*_r(G) → B(ℓ²(G))`, as a linear map. -/
def regInclusion : ReducedGroupCStar G →ₗ[ℂ] (GroupHilbert G →L[ℂ] GroupHilbert G) where
  toFun c := (c : GroupHilbert G →L[ℂ] GroupHilbert G)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem regInclusion_reducedLeftRegular (g : G) :
    regInclusion G (reducedLeftRegular G g) = leftRegularOperator G g :=
  rfl

end Operators

section Amplify

variable {A : Type*} [Ring A] [Algebra ℂ A] {C : Type*} [Ring C] [Algebra ℂ C]
  {D : Type*} [Ring D] [Algebra ℂ D]

/-- Amplifying a linear map in the second leg commutes with right
multiplication by `b ⊗ 1`. -/
theorem lTensor_mul_tmul_one (Ψ : C →ₗ[ℂ] D) (x : A ⊗[ℂ] C) (b : A) :
    LinearMap.lTensor A Ψ (x * (b ⊗ₜ[ℂ] (1 : C)))
      = LinearMap.lTensor A Ψ x * (b ⊗ₜ[ℂ] (1 : D)) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [zero_mul, map_zero, zero_mul]
  | tmul a c =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, LinearMap.lTensor_tmul,
        LinearMap.lTensor_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  | add x₁ x₂ h₁ h₂ => rw [add_mul, map_add, map_add, add_mul, h₁, h₂]

end Amplify

section IdealSide

/-- Right multiplication by `e ⊗ 1` with `e ∈ I` lands in `I ⊙ C`. -/
theorem minTensorIn_mul_tmul_one_mem {B : Type u} [CStarAlgebra B] [Nontrivial B]
    {C : Type v} [CStarAlgebra C] [Nontrivial C] (I : Ideal B) [I.IsTwoSided]
    [IsStarStable I] [IsClosed (I : Set B)] [Nontrivial (B ⧸ I)] (x : B ⊗[ℂ] C) {e : B}
    (he : e ∈ I) :
    minTensorIn B C (x * (e ⊗ₜ[ℂ] (1 : C))) ∈ idealTensorSpan (C := C) I := by
  induction x using TensorProduct.induction_on with
  | zero =>
      rw [zero_mul, map_zero]
      exact Submodule.zero_mem _
  | tmul b c =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      have hmem : minTensorIn B C ((b * e) ⊗ₜ[ℂ] c) ∈
          {w : MinTensorProduct B C | ∃ b' c', b' ∈ I ∧ w = minTensorIn B C (b' ⊗ₜ[ℂ] c')} :=
        ⟨b * e, c, I.mul_mem_left b he, rfl⟩
      exact Submodule.subset_span hmem
  | add x₁ x₂ h₁ h₂ =>
      rw [add_mul, map_add]
      exact Submodule.add_mem _ h₁ h₂

/-- **An approximate unit absorbs finitely many ideal elements at once**, from
below the unit. -/
theorem exists_approxUnit_absorb {B : Type u} [CStarAlgebra B] [Nontrivial B] (I : Ideal B)
    [I.IsTwoSided] [IsStarStable I] [IsClosed (I : Set B)] {ι : Type*} (S : Finset ι)
    (b : ι → B) (hb : ∀ i ∈ S, b i ∈ I) {δ : ℝ} (hδ : 0 < δ) :
    ∃ e : B, e ∈ I ∧ ‖(1 : B) - e‖ ≤ 1 ∧ ∀ i ∈ S, ‖b i - b i * e‖ < δ := by
  have U : IdealApproximateUnit I := idealApproximateUnit I
  haveI : U.filter.NeBot := U.neBot
  have hS : ∀ᶠ e in U.filter, ∀ i ∈ S, ‖b i - b i * e‖ < δ :=
    (Filter.eventually_all_finset S).2 fun i hi ↦
      (U.tendsto_mul_right (b i) (hb i hi)).eventually (gt_mem_nhds hδ)
  obtain ⟨e, he, h1, h2⟩ := (U.eventually_mem.and (U.eventually_norm_one_sub.and hS)).exists
  exact ⟨e, he, h1, h2⟩

end IdealSide

section Estimates

variable {G : Type u} [Group G] {R : Finset G} {ε : ℝ}
variable {B : Type v} [CStarAlgebra B]

local instance decEqExactnessEstimates : DecidableEq G := Classical.decEq G

/-- The defect `J - Φ` of the Schur multiplier. -/
def schurDefect (W : PropertyAWitness G R ε) :
    ReducedGroupCStar G →ₗ[ℂ] (GroupHilbert G →L[ℂ] GroupHilbert G) :=
  regInclusion G - schurMultiplier W

/-- `id ⊗ J` is isometric on `B ⊗ C*_r(G)`. -/
theorem minTensorNorm_lTensor_regInclusion [Nontrivial B] (y : B ⊗[ℂ] ReducedGroupCStar G) :
    minTensorNorm (LinearMap.lTensor B (regInclusion G) y) = minTensorNorm y := by
  haveI : Nontrivial (GroupHilbert G →L[ℂ] GroupHilbert G) := nontrivial_groupOperators G
  exact minTensorNorm_lTensor_of_injective (reducedGroupCStarSubalgebra G).subtype
    (fun _ _ h ↦ Subtype.ext h) (regInclusion G) (fun _ ↦ rfl) y

/-- `id ⊗ Φ` is contractive on `B ⊗ C*_r(G)`. -/
theorem minTensorNorm_lTensor_schurMultiplier_le [Nontrivial B] (W : PropertyAWitness G R ε)
    (y : B ⊗[ℂ] ReducedGroupCStar G) :
    minTensorNorm (LinearMap.lTensor B (schurMultiplier W) y) ≤ minTensorNorm y := by
  haveI : Nontrivial (GroupHilbert G →L[ℂ] GroupHilbert G) := nontrivial_groupOperators G
  exact minTensorNorm_lTensor_compress_le (ampRegRep G) (schurDilation W)
    (norm_schurDilation_le W) (schurMultiplier W) (schurMultiplier_apply W) y

/-- `id ⊗ J = id ⊗ (J - Φ) + id ⊗ Φ`. -/
theorem lTensor_regInclusion_eq (W : PropertyAWitness G R ε)
    (y : B ⊗[ℂ] ReducedGroupCStar G) :
    LinearMap.lTensor B (regInclusion G) y
      = LinearMap.lTensor B (schurDefect W) y + LinearMap.lTensor B (schurMultiplier W) y := by
  rw [schurDefect, LinearMap.lTensor_sub, LinearMap.sub_apply, sub_add_cancel]

/-- `‖id ⊗ (J - Φ)‖ ≤ 2`. -/
theorem minTensorNorm_lTensor_schurDefect_le [Nontrivial B] (W : PropertyAWitness G R ε)
    (y : B ⊗[ℂ] ReducedGroupCStar G) :
    minTensorNorm (LinearMap.lTensor B (schurDefect W) y) ≤ 2 * minTensorNorm y := by
  have h : LinearMap.lTensor B (schurDefect W) y
      = LinearMap.lTensor B (regInclusion G) y - LinearMap.lTensor B (schurMultiplier W) y := by
    rw [schurDefect, LinearMap.lTensor_sub, LinearMap.sub_apply]
  calc minTensorNorm (LinearMap.lTensor B (schurDefect W) y)
      = ‖minTensorIn B (GroupHilbert G →L[ℂ] GroupHilbert G)
            (LinearMap.lTensor B (regInclusion G) y)
          - minTensorIn B (GroupHilbert G →L[ℂ] GroupHilbert G)
            (LinearMap.lTensor B (schurMultiplier W) y)‖ := by
        rw [h, ← norm_minTensorIn, map_sub (minTensorIn B (GroupHilbert G →L[ℂ] GroupHilbert G))]
    _ ≤ ‖minTensorIn B (GroupHilbert G →L[ℂ] GroupHilbert G)
            (LinearMap.lTensor B (regInclusion G) y)‖
          + ‖minTensorIn B (GroupHilbert G →L[ℂ] GroupHilbert G)
            (LinearMap.lTensor B (schurMultiplier W) y)‖ := norm_sub_le _ _
    _ ≤ minTensorNorm y + minTensorNorm y := by
        rw [norm_minTensorIn, norm_minTensorIn, minTensorNorm_lTensor_regInclusion]
        exact add_le_add le_rfl (minTensorNorm_lTensor_schurMultiplier_le W y)
    _ = 2 * minTensorNorm y := (two_mul _).symm

/-- `id ⊗ Ψ` on a translation form: `∑_g f(g) ⊗ Ψ(λ_g)`. -/
theorem lTensor_translationForm {D : Type*} [AddCommGroup D] [Module ℂ D]
    (Ψ : ReducedGroupCStar G →ₗ[ℂ] D) (f : G →₀ B) :
    LinearMap.lTensor B Ψ (translationForm G B f)
      = ∑ g ∈ f.support, f g ⊗ₜ[ℂ] Ψ (reducedLeftRegular G g) := by
  rw [translationForm, Finsupp.lsum_apply, Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun g _ ↦ ?_
  rw [LinearMap.flip_apply, TensorProduct.mk_apply, LinearMap.lTensor_tmul]

/-- **The defect is small on short translation forms**. -/
theorem norm_minTensorIn_lTensor_schurDefect_translationForm_le (W : PropertyAWitness G R ε)
    (f : G →₀ B) (hf : f.support ⊆ R) :
    ‖minTensorIn B (GroupHilbert G →L[ℂ] GroupHilbert G)
        (LinearMap.lTensor B (schurDefect W) (translationForm G B f))‖
      ≤ (∑ g ∈ f.support, ‖f g‖) * (ε / 2) := by
  rw [lTensor_translationForm, map_sum (minTensorIn B (GroupHilbert G →L[ℂ] GroupHilbert G)),
    Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun g hg ↦ ?_)
  rw [norm_minTensorIn_tmul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [schurDefect, LinearMap.sub_apply, regInclusion_reducedLeftRegular]
  exact norm_leftRegular_sub_schurMultiplier_le W (hf hg)

/-- **The multiplier only sees the difference set**. -/
theorem lTensor_schurMultiplier_translationForm (W : PropertyAWitness G R ε) (f : G →₀ B) :
    LinearMap.lTensor B (schurMultiplier W) (translationForm G B f)
      = ∑ g ∈ diffSet W, f g ⊗ₜ[ℂ] schurMultiplier W (reducedLeftRegular G g) := by
  rw [lTensor_translationForm]
  have h1 : ∑ g ∈ f.support, f g ⊗ₜ[ℂ] schurMultiplier W (reducedLeftRegular G g)
      = ∑ g ∈ f.support ∪ diffSet W,
          f g ⊗ₜ[ℂ] schurMultiplier W (reducedLeftRegular G g) :=
    Finset.sum_subset Finset.subset_union_left fun g _ hg ↦ by
      rw [Finsupp.notMem_support_iff.mp hg, TensorProduct.zero_tmul]
  have h2 : ∑ g ∈ diffSet W, f g ⊗ₜ[ℂ] schurMultiplier W (reducedLeftRegular G g)
      = ∑ g ∈ f.support ∪ diffSet W,
          f g ⊗ₜ[ℂ] schurMultiplier W (reducedLeftRegular G g) :=
    Finset.sum_subset Finset.subset_union_right fun g _ hg ↦ by
      rw [schurMultiplier_reducedLeftRegular_eq_zero W hg, TensorProduct.tmul_zero]
  rw [h1, h2]

/-- **The splitting estimate**: `‖y (1 - e) ⊗ 1‖ ≤ ‖(id ⊗ (J - Φ)) y‖ +
‖(id ⊗ Φ)(y ((1 - e) ⊗ 1))‖` whenever `‖1 - e‖ ≤ 1`. -/
theorem norm_lTensor_regInclusion_mul_le [Nontrivial B] (W : PropertyAWitness G R ε)
    (x : B ⊗[ℂ] ReducedGroupCStar G) {e : B} (he1 : ‖(1 : B) - e‖ ≤ 1) :
    ‖minTensorIn B (ReducedGroupCStar G) (x * ((1 - e) ⊗ₜ[ℂ] (1 : ReducedGroupCStar G)))‖
      ≤ ‖minTensorIn B (GroupHilbert G →L[ℂ] GroupHilbert G)
            (LinearMap.lTensor B (schurDefect W) x)‖
        + ‖minTensorIn B (GroupHilbert G →L[ℂ] GroupHilbert G)
            (LinearMap.lTensor B (schurMultiplier W)
              (x * ((1 - e) ⊗ₜ[ℂ] (1 : ReducedGroupCStar G))))‖ := by
  haveI : Nontrivial (GroupHilbert G →L[ℂ] GroupHilbert G) := nontrivial_groupOperators G
  have hJ : ‖minTensorIn B (ReducedGroupCStar G)
        (x * ((1 - e) ⊗ₜ[ℂ] (1 : ReducedGroupCStar G)))‖
      = ‖minTensorIn B (GroupHilbert G →L[ℂ] GroupHilbert G) (LinearMap.lTensor B
          (regInclusion G) (x * ((1 - e) ⊗ₜ[ℂ] (1 : ReducedGroupCStar G))))‖ := by
    rw [norm_minTensorIn, norm_minTensorIn, minTensorNorm_lTensor_regInclusion]
  have hsplit : LinearMap.lTensor B (regInclusion G)
        (x * ((1 - e) ⊗ₜ[ℂ] (1 : ReducedGroupCStar G)))
      = LinearMap.lTensor B (schurDefect W) x
          * ((1 - e) ⊗ₜ[ℂ] (1 : GroupHilbert G →L[ℂ] GroupHilbert G))
        + LinearMap.lTensor B (schurMultiplier W)
          (x * ((1 - e) ⊗ₜ[ℂ] (1 : ReducedGroupCStar G))) := by
    rw [lTensor_regInclusion_eq W, lTensor_mul_tmul_one (schurDefect W) x (1 - e)]
  calc ‖minTensorIn B (ReducedGroupCStar G)
          (x * ((1 - e) ⊗ₜ[ℂ] (1 : ReducedGroupCStar G)))‖
      = ‖minTensorIn B (GroupHilbert G →L[ℂ] GroupHilbert G)
            (LinearMap.lTensor B (schurDefect W) x)
          * minTensorIn B (GroupHilbert G →L[ℂ] GroupHilbert G)
            ((1 - e) ⊗ₜ[ℂ] (1 : GroupHilbert G →L[ℂ] GroupHilbert G))
          + minTensorIn B (GroupHilbert G →L[ℂ] GroupHilbert G)
            (LinearMap.lTensor B (schurMultiplier W)
              (x * ((1 - e) ⊗ₜ[ℂ] (1 : ReducedGroupCStar G))))‖ := by
        rw [hJ, hsplit, map_add (minTensorIn B (GroupHilbert G →L[ℂ] GroupHilbert G)),
          map_mul (minTensorIn B (GroupHilbert G →L[ℂ] GroupHilbert G))]
    _ ≤ ‖minTensorIn B (GroupHilbert G →L[ℂ] GroupHilbert G)
            (LinearMap.lTensor B (schurDefect W) x)‖
          * ‖minTensorIn B (GroupHilbert G →L[ℂ] GroupHilbert G)
            ((1 - e) ⊗ₜ[ℂ] (1 : GroupHilbert G →L[ℂ] GroupHilbert G))‖
          + ‖minTensorIn B (GroupHilbert G →L[ℂ] GroupHilbert G)
            (LinearMap.lTensor B (schurMultiplier W)
              (x * ((1 - e) ⊗ₜ[ℂ] (1 : ReducedGroupCStar G))))‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) le_rfl)
    _ ≤ _ := by
        rw [norm_minTensorIn_tmul, norm_one, mul_one]
        exact add_le_add (mul_le_of_le_one_right (norm_nonneg _) he1) le_rfl

/-- **The multiplier part is controlled by the difference set**. -/
theorem norm_lTensor_schurMultiplier_mul_le (W : PropertyAWitness G R ε) (f : G →₀ B) (e : B)
    {η : ℝ} (hη : ∀ g ∈ diffSet W, ‖f g * (1 - e)‖ ≤ η) :
    ‖minTensorIn B (GroupHilbert G →L[ℂ] GroupHilbert G)
        (LinearMap.lTensor B (schurMultiplier W)
          (translationForm G B f * ((1 - e) ⊗ₜ[ℂ] (1 : ReducedGroupCStar G))))‖
      ≤ (diffSet W).card * η := by
  rw [lTensor_mul_tmul_one, lTensor_schurMultiplier_translationForm, Finset.sum_mul,
    map_sum (minTensorIn B (GroupHilbert G →L[ℂ] GroupHilbert G))]
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ g ∈ diffSet W, ‖minTensorIn B (GroupHilbert G →L[ℂ] GroupHilbert G)
      ((f g ⊗ₜ[ℂ] schurMultiplier W (reducedLeftRegular G g))
        * ((1 - e) ⊗ₜ[ℂ] (1 : GroupHilbert G →L[ℂ] GroupHilbert G)))‖ ≤ η := by
    intro g hg
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, norm_minTensorIn_tmul]
    exact (mul_le_of_le_one_right (norm_nonneg _)
      (norm_schurMultiplier_reducedLeftRegular_le W g)).trans (hη g hg)
  refine (Finset.sum_le_sum h).trans_eq ?_
  rw [Finset.sum_const, nsmul_eq_mul]

/-- **The defect part is controlled by two approximants**: a short
translation form `f₁` and a nearby translation form `f₂`. -/
theorem norm_lTensor_schurDefect_le_of_near [Nontrivial B] (W : PropertyAWitness G R ε)
    (f₁ f₂ : G →₀ B) (hf₁ : f₁.support ⊆ R) (z : MinTensorProduct B (ReducedGroupCStar G)) :
    ‖minTensorIn B (GroupHilbert G →L[ℂ] GroupHilbert G)
        (LinearMap.lTensor B (schurDefect W) (translationForm G B f₂))‖
      ≤ (∑ g ∈ f₁.support, ‖f₁ g‖) * (ε / 2)
        + 2 * (‖z - minTensorIn B (ReducedGroupCStar G) (translationForm G B f₁)‖
          + ‖z - minTensorIn B (ReducedGroupCStar G) (translationForm G B f₂)‖) := by
  have hsplit : LinearMap.lTensor B (schurDefect W) (translationForm G B f₂)
      = LinearMap.lTensor B (schurDefect W) (translationForm G B f₁)
        + LinearMap.lTensor B (schurDefect W)
          (translationForm G B f₂ - translationForm G B f₁) := by
    rw [map_sub]
    abel
  have h2 : ‖minTensorIn B (GroupHilbert G →L[ℂ] GroupHilbert G)
        (LinearMap.lTensor B (schurDefect W)
          (translationForm G B f₂ - translationForm G B f₁))‖
      ≤ 2 * (‖z - minTensorIn B (ReducedGroupCStar G) (translationForm G B f₁)‖
          + ‖z - minTensorIn B (ReducedGroupCStar G) (translationForm G B f₂)‖) := by
    rw [norm_minTensorIn]
    refine (minTensorNorm_lTensor_schurDefect_le W _).trans ?_
    rw [← norm_minTensorIn, map_sub (minTensorIn B (ReducedGroupCStar G))]
    have h3 : minTensorIn B (ReducedGroupCStar G) (translationForm G B f₂)
          - minTensorIn B (ReducedGroupCStar G) (translationForm G B f₁)
        = (z - minTensorIn B (ReducedGroupCStar G) (translationForm G B f₁))
          - (z - minTensorIn B (ReducedGroupCStar G) (translationForm G B f₂)) := by
      abel
    rw [h3]
    exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) zero_le_two
  rw [hsplit, map_add (minTensorIn B (GroupHilbert G →L[ℂ] GroupHilbert G))]
  exact (norm_add_le _ _).trans
    (add_le_add (norm_minTensorIn_lTensor_schurDefect_translationForm_le W f₁ hf₁) h2)

end Estimates

end

end GroupApproximation.Full.NN09c
