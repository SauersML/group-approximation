import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ChoiEffrosCPBasics
import GroupApproximation.Analysis.BlackadarKirchbergFiniteDirectSumLift
import Mathlib.Tactic.NoncommRing

/-!
# Choi–Effros lifting, the Arveson splicing step

Lane `TWWSchafhauser-3a` (work order `WO-TWWCore-3`, piece 3a).

Let `f, g` be self-adjoint contractions with `f² + g² = 1`, `π f = 1` and
`π g = 0` (an *Arveson pair*, `exists_arvesonPair`).  Given two completely
positive contractions `ψ₁, ψ₀ : A → B`, the splice

`ψ(a) = f ψ₁(a) f + g ψ₀(a) g`

is again a completely positive contraction, it has the same image under `π` as
`ψ₁`, and it is close to `ψ₀`:

`‖ψ(a) - ψ₀(a)‖ ≤ ‖f² (ψ₁ a - ψ₀ a)‖ + ‖f ψ₁(a) - ψ₁(a) f‖ + ‖g ψ₀(a) - ψ₀(a) g‖`.

So when `f` almost commutes with the values and `f²` almost kills the kernel
part of `ψ₁ - ψ₀`, the splice moves `ψ₀` only a little while taking over the
quotient behaviour of `ψ₁`.  This is the key step of Arveson's proof that the
point-norm limits of liftable maps are liftable.

Sources: W. Arveson, *Notes on extensions of C⋆-algebras*, Duke Math. J. **44**
(1977), 329–355, §2 (Theorem 6 and its proof); N. P. Brown, N. Ozawa,
*C⋆-algebras and finite-dimensional approximations*, Lemma C.2.
-/

namespace GroupApproximation
namespace Full
namespace TWWSchafhauser

noncomputable section

universe u v w

/-! ## The splicing identity -/

section Ring

variable {B : Type v} [NormedRing B]

/-- The splicing identity: with `f² + g² = 1`,
`f y₁ f + g y₀ g - y₀ = f² (y₁ - y₀) - f (f y₁ - y₁ f) - g (g y₀ - y₀ g)`. -/
theorem arveson_combination_sub_eq {f g y₀ y₁ : B} (hfg : f * f + g * g = 1) :
    f * y₁ * f + g * y₀ * g - y₀ =
      f * f * (y₁ - y₀) - f * (f * y₁ - y₁ * f) - g * (g * y₀ - y₀ * g) := by
  have hid : f * f * (y₁ - y₀) - f * (f * y₁ - y₁ * f) - g * (g * y₀ - y₀ * g) =
      f * y₁ * f + g * y₀ * g - (f * f + g * g) * y₀ := by
    noncomm_ring
  rw [hfg, one_mul] at hid
  exact hid.symm

/-- The splicing estimate for contractions `f`, `g` with `f² + g² = 1`. -/
theorem norm_arveson_combination_sub_le {f g y₀ y₁ : B} (hf : ‖f‖ ≤ 1) (hg : ‖g‖ ≤ 1)
    (hfg : f * f + g * g = 1) :
    ‖f * y₁ * f + g * y₀ * g - y₀‖ ≤
      ‖f * f * (y₁ - y₀)‖ + ‖f * y₁ - y₁ * f‖ + ‖g * y₀ - y₀ * g‖ := by
  have hmul : ∀ c : B, ‖c‖ ≤ 1 → ∀ z : B, ‖c * z‖ ≤ ‖z‖ := fun c hc z ↦
    (norm_mul_le c z).trans (mul_le_of_le_one_left (norm_nonneg z) hc)
  rw [arveson_combination_sub_eq hfg]
  calc ‖f * f * (y₁ - y₀) - f * (f * y₁ - y₁ * f) - g * (g * y₀ - y₀ * g)‖
      ≤ ‖f * f * (y₁ - y₀) - f * (f * y₁ - y₁ * f)‖ + ‖g * (g * y₀ - y₀ * g)‖ :=
        norm_sub_le _ _
    _ ≤ ‖f * f * (y₁ - y₀)‖ + ‖f * (f * y₁ - y₁ * f)‖ + ‖g * (g * y₀ - y₀ * g)‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ ‖f * f * (y₁ - y₀)‖ + ‖f * y₁ - y₁ * f‖ + ‖g * y₀ - y₀ * g‖ :=
        add_le_add (add_le_add le_rfl (hmul f hf _)) (hmul g hg _)

end Ring

/-! ## The splice of two completely positive maps -/

section Splice

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]

/-- The Arveson splice `a ↦ f⋆ ψ₁(a) f + g⋆ ψ₀(a) g`. -/
def arvesonCombination (f g : B) (ψ₁ ψ₀ : A →ₗ[ℂ] B) : A →ₗ[ℂ] B :=
  compressLinearMap f ψ₁ + compressLinearMap g ψ₀

theorem arvesonCombination_apply (f g : B) (ψ₁ ψ₀ : A →ₗ[ℂ] B) (a : A) :
    arvesonCombination f g ψ₁ ψ₀ a = star f * ψ₁ a * f + star g * ψ₀ a * g := rfl

/-- The splice of completely positive maps is completely positive. -/
theorem isCompletelyPositive_arvesonCombination (f g : B) {ψ₁ ψ₀ : A →ₗ[ℂ] B}
    (h₁ : CStarExactness.IsCompletelyPositive ψ₁)
    (h₀ : CStarExactness.IsCompletelyPositive ψ₀) :
    CStarExactness.IsCompletelyPositive (arvesonCombination f g ψ₁ ψ₀) :=
  BlackadarKirchberg.CStarExactness.IsCompletelyPositive.add
    (isCompletelyPositive_compressLinearMap f h₁) (isCompletelyPositive_compressLinearMap g h₀)

/-- The splice of completely positive contractions along an Arveson pair has
`‖ψ(1)‖ ≤ 1`: `0 ≤ f ψ₁(1) f + g ψ₀(1) g ≤ f² + g² = 1`. -/
theorem norm_arvesonCombination_map_one_le {f g : B} (hf : IsSelfAdjoint f)
    (hg : IsSelfAdjoint g) (hfg : f * f + g * g = 1) {ψ₁ ψ₀ : A →ₗ[ℂ] B}
    (h₁ : CStarExactness.IsCompletelyPositive ψ₁)
    (h₀ : CStarExactness.IsCompletelyPositive ψ₀)
    (h₁c : ‖ψ₁ 1‖ ≤ 1) (h₀c : ‖ψ₀ 1‖ ≤ 1) :
    ‖arvesonCombination f g ψ₁ ψ₀ 1‖ ≤ 1 := by
  letI : PartialOrder B := CStarAlgebra.spectralOrder B
  letI : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  have hunit : ∀ {L : A →ₗ[ℂ] B}, CStarExactness.IsCompletelyPositive L →
      ‖L 1‖ ≤ 1 → 0 ≤ L 1 ∧ L 1 ≤ 1 := by
    intro L hL hLc
    obtain ⟨p, hp⟩ := exists_map_star_mul_self_eq hL (1 : A)
    rw [star_one, one_mul] at hp
    have hnn : 0 ≤ L 1 := by
      rw [hp]
      exact star_mul_self_nonneg p
    exact ⟨hnn, (CStarAlgebra.norm_le_one_iff_of_nonneg (L 1) hnn).mp hLc⟩
  obtain ⟨h₁nn, h₁le⟩ := hunit h₁ h₁c
  obtain ⟨h₀nn, h₀le⟩ := hunit h₀ h₀c
  have hnn : 0 ≤ arvesonCombination f g ψ₁ ψ₀ 1 := by
    rw [arvesonCombination_apply]
    exact add_nonneg (star_left_conjugate_nonneg h₁nn f) (star_left_conjugate_nonneg h₀nn g)
  have hle : arvesonCombination f g ψ₁ ψ₀ 1 ≤ 1 := by
    rw [arvesonCombination_apply]
    calc star f * ψ₁ 1 * f + star g * ψ₀ 1 * g
        ≤ star f * 1 * f + star g * 1 * g :=
          add_le_add (star_left_conjugate_le_conjugate h₁le f)
            (star_left_conjugate_le_conjugate h₀le g)
      _ = 1 := by rw [mul_one, mul_one, hf.star_eq, hg.star_eq, hfg]
  exact (CStarAlgebra.norm_le_one_iff_of_nonneg _ hnn).mpr hle

/-- The splice of completely positive contractions along an Arveson pair is
contractive. -/
theorem norm_arvesonCombination_apply_le {f g : B} (hf : IsSelfAdjoint f)
    (hg : IsSelfAdjoint g) (hfg : f * f + g * g = 1) {ψ₁ ψ₀ : A →ₗ[ℂ] B}
    (h₁ : CStarExactness.IsCompletelyPositive ψ₁)
    (h₀ : CStarExactness.IsCompletelyPositive ψ₀)
    (h₁c : ‖ψ₁ 1‖ ≤ 1) (h₀c : ‖ψ₀ 1‖ ≤ 1) (a : A) :
    ‖arvesonCombination f g ψ₁ ψ₀ a‖ ≤ ‖a‖ :=
  norm_apply_le_of_norm_map_one_le (isCompletelyPositive_arvesonCombination f g h₁ h₀)
    (norm_arvesonCombination_map_one_le hf hg hfg h₁ h₀ h₁c h₀c) a

/-- Along an Arveson pair, the splice has the quotient image of `ψ₁`. -/
theorem map_arvesonCombination {C : Type w} [CStarAlgebra C] (π : B →⋆ₐ[ℂ] C) {f g : B}
    (hπf : π f = 1) (hπg : π g = 0) (ψ₁ ψ₀ : A →ₗ[ℂ] B) (a : A) :
    π (arvesonCombination f g ψ₁ ψ₀ a) = π (ψ₁ a) := by
  rw [arvesonCombination_apply, map_add, map_mul, map_mul, map_mul, map_mul, map_star,
    map_star, hπf, hπg, star_one, star_zero, one_mul, mul_one, zero_mul, zero_mul, add_zero]

/-- Along an Arveson pair, the splice stays close to `ψ₀`. -/
theorem norm_arvesonCombination_sub_le {f g : B} (hf : IsSelfAdjoint f)
    (hg : IsSelfAdjoint g) (hf1 : ‖f‖ ≤ 1) (hg1 : ‖g‖ ≤ 1) (hfg : f * f + g * g = 1)
    (ψ₁ ψ₀ : A →ₗ[ℂ] B) (a : A) :
    ‖arvesonCombination f g ψ₁ ψ₀ a - ψ₀ a‖ ≤
      ‖f * f * (ψ₁ a - ψ₀ a)‖ + ‖f * ψ₁ a - ψ₁ a * f‖ + ‖g * ψ₀ a - ψ₀ a * g‖ := by
  rw [arvesonCombination_apply, hf.star_eq, hg.star_eq]
  exact norm_arveson_combination_sub_le hf1 hg1 hfg

end Splice

end

end TWWSchafhauser
end Full
end GroupApproximation
