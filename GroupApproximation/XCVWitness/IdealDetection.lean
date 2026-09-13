import GroupApproximation.Analysis.CStarSimple
import GroupApproximation.Analysis.CStarIdealApproximateUnit
import GroupApproximation.Analysis.CStarQuotientHom
import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Detecting ideals through a subalgebra

A ⋆-homomorphism `ι : C →⋆ₐ[ℂ] D` of unital C⋆-algebras *detects ideals* when every nonzero
positive element `a⋆a` of `D` can be compressed onto the image of a nonzero `d ∈ C`, up to any
`ε > 0`, without losing the norm of `d`:

  `‖ι f · a⋆a · ι g − ι (f d g)‖ ≤ ε`  and  `‖d‖ ≤ ‖f d g‖ + ε`.

`isSimpleCStar_of_detectsIdeals`: if `ι` detects ideals and `C` is simple, then `D` is simple.
This is the abstract form of "an outer action gives a simple crossed product". For `D = C ⋊ ℤ`
the element `d` is the conditional expectation of `a⋆a`, and `f, g` come from Kishimoto's
condition (`XCVWitness/KishimotoSimple`).

The proof works with the star part `J ∩ J⋆` of a nonzero closed ideal `J` of `D`, which contains
`b⋆b ≠ 0` for any nonzero `b ∈ J`.
* If `ι` meets `J ∩ J⋆` in a nonzero element, then simplicity of `C` gives `1 ∈ J`.
* Otherwise `C → D → D ⧸ (J ∩ J⋆)` is an injective ⋆-homomorphism of C⋆-algebras, so it is
  isometric. Then `ι f · b⋆b · ι g ∈ J` forces `‖f d g‖ ≤ ε`, so `‖d‖ ≤ 2ε` for every `ε`.
-/

namespace GroupApproximation
namespace XCVWitness

open CStarTensor

section StarPart

variable {D : Type*} [CStarAlgebra D]

/-- The star part `J ∩ J⋆` of a two-sided ideal: the largest star-stable ideal inside `J`. -/
def starPart (J : Ideal D) [J.IsTwoSided] : Ideal D where
  carrier := {x | x ∈ J ∧ star x ∈ J}
  add_mem' hx hy := ⟨J.add_mem hx.1 hy.1, by rw [star_add]; exact J.add_mem hx.2 hy.2⟩
  zero_mem' := ⟨J.zero_mem, by rw [star_zero]; exact J.zero_mem⟩
  smul_mem' c _ hx := ⟨J.mul_mem_left c hx.1, by
    rw [smul_eq_mul, star_mul]; exact Ideal.mul_mem_right (star c) J hx.2⟩

variable (J : Ideal D) [J.IsTwoSided]

theorem mem_starPart {x : D} : x ∈ starPart J ↔ x ∈ J ∧ star x ∈ J := Iff.rfl

instance isTwoSided_starPart : (starPart J).IsTwoSided where
  mul_mem_of_left b ha := by
    obtain ⟨h1, h2⟩ := (mem_starPart J).1 ha
    refine (mem_starPart J).2 ⟨Ideal.mul_mem_right b J h1, ?_⟩
    rw [star_mul]
    exact J.mul_mem_left (star b) h2

instance isStarStable_starPart : IsStarStable (starPart J) where
  star_mem ha := by
    obtain ⟨h1, h2⟩ := (mem_starPart J).1 ha
    exact (mem_starPart J).2 ⟨h2, by rw [star_star]; exact h1⟩

instance isClosed_starPart [hJ : IsClosed (J : Set D)] : IsClosed (starPart J : Set D) := by
  have h : (starPart J : Set D) = (J : Set D) ∩ star ⁻¹' (J : Set D) :=
    Set.ext fun _ => Iff.rfl
  rw [h]
  exact IsClosed.inter hJ (IsClosed.preimage continuous_star hJ)

theorem star_mul_self_mem_starPart {b : D} (hb : b ∈ J) : star b * b ∈ starPart J :=
  (mem_starPart J).2 ⟨J.mul_mem_left (star b) hb, by
    rw [star_mul, star_star]; exact J.mul_mem_left (star b) hb⟩

end StarPart

section Detection

variable {C D : Type*} [CStarAlgebra C] [CStarAlgebra D]

/-- `ι` detects ideals: every nonzero `a⋆a` compresses, up to `ε`, onto the image of a fixed
nonzero `d ∈ C` without losing the norm of `d`. -/
def DetectsIdeals (ι : C →⋆ₐ[ℂ] D) : Prop :=
  ∀ a : D, a ≠ 0 → ∃ d : C, d ≠ 0 ∧ ∀ ε : ℝ, 0 < ε →
    ∃ f g : C, ‖ι f * (star a * a) * ι g - ι (f * d * g)‖ ≤ ε ∧ ‖d‖ ≤ ‖f * d * g‖ + ε

/-- **Ideal detection transfers simplicity.** -/
theorem isSimpleCStar_of_detectsIdeals [Nontrivial D] (hC : IsSimpleCStar C)
    (ι : C →⋆ₐ[ℂ] D) (hdet : DetectsIdeals ι) : IsSimpleCStar D := by
  intro J hJ hJc
  by_cases hbot : J = ⊥
  · exact Or.inl hbot
  refine Or.inr ?_
  obtain ⟨b, hbJ, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  have hx := star_mul_self_mem_starPart J hbJ
  by_cases hmeet : ∃ c : C, c ≠ 0 ∧ ι c ∈ starPart J
  · obtain ⟨c, hc0, hcJ⟩ := hmeet
    have hcont : Continuous ι := AddMonoidHomClass.continuous_of_bound ι 1 fun x => by
      rw [one_mul]; exact NonUnitalStarAlgHom.norm_apply_le ι x
    have hclosed : IsClosed (Ideal.comap ι (starPart J) : Set C) :=
      IsClosed.preimage hcont (isClosed_starPart J)
    have htop := hC.eq_top_of_mem hclosed (Ideal.mem_comap.2 hcJ) hc0
    have h1 : (1 : C) ∈ Ideal.comap ι (starPart J) := by
      rw [htop]; exact Submodule.mem_top
    rw [Ideal.mem_comap, map_one] at h1
    exact (Ideal.eq_top_iff_one J).2 ((mem_starPart J).1 h1).1
  · have hmeet' : ∀ c : C, c ≠ 0 → ι c ∉ starPart J := fun c hc hcJ => hmeet ⟨c, hc, hcJ⟩
    have hinj : Function.Injective ((quotientStarMk (starPart J)).comp ι) := by
      intro c₁ c₂ h
      rw [StarAlgHom.comp_apply, StarAlgHom.comp_apply, quotientStarMk_apply,
        quotientStarMk_apply] at h
      by_contra hne
      refine hmeet' (c₁ - c₂) (sub_ne_zero.2 hne) ?_
      rw [map_sub]
      exact Ideal.Quotient.eq.1 h
    obtain ⟨d, hd0, hd⟩ := hdet b hb0
    have hdpos : 0 < ‖d‖ := norm_pos_iff.2 hd0
    obtain ⟨f, g, hfg, hlow⟩ := hd (‖d‖ / 3) (by linarith)
    have hmem : ι f * (star b * b) * ι g ∈ starPart J :=
      Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hx)
    have hq : quotientStarMk (starPart J) (ι f * (star b * b) * ι g) = 0 := by
      rw [quotientStarMk_apply]
      exact Ideal.Quotient.eq_zero_iff_mem.2 hmem
    have hup : ‖f * d * g‖ ≤ ‖d‖ / 3 := by
      rw [← NonUnitalStarAlgHom.norm_map ((quotientStarMk (starPart J)).comp ι) hinj (f * d * g),
        StarAlgHom.comp_apply]
      calc ‖quotientStarMk (starPart J) (ι (f * d * g))‖
          = ‖quotientStarMk (starPart J) (ι (f * d * g) - ι f * (star b * b) * ι g)‖ := by
            rw [map_sub, hq, sub_zero]
        _ ≤ ‖ι (f * d * g) - ι f * (star b * b) * ι g‖ := NonUnitalStarAlgHom.norm_apply_le _ _
        _ = ‖ι f * (star b * b) * ι g - ι (f * d * g)‖ := norm_sub_rev _ _
        _ ≤ ‖d‖ / 3 := hfg
    exfalso
    linarith

/-- Model test (positive): the identity detects ideals, with `d = a⋆a` and `f = g = 1`. -/
theorem detectsIdeals_id : DetectsIdeals (StarAlgHom.id ℂ D) := by
  intro a ha
  refine ⟨star a * a, (CStarRing.star_mul_self_ne_zero_iff a).2 ha, fun ε hε => ⟨1, 1, ?_, ?_⟩⟩
  · simpa using hε.le
  · rw [one_mul, mul_one]; linarith

/-- Model test (negative): the diagonal `ℂ → ℂ × ℂ` does not detect ideals, as it must not,
since `ℂ × ℂ` is not simple. -/
theorem not_detectsIdeals_diag :
    ¬ DetectsIdeals ((StarAlgHom.id ℂ ℂ).prod (StarAlgHom.id ℂ ℂ)) := by
  intro h
  obtain ⟨d, hd0, hd⟩ := h ((1 : ℂ), (0 : ℂ)) fun h0 => one_ne_zero (congrArg Prod.fst h0)
  have hdpos : 0 < ‖d‖ := norm_pos_iff.2 hd0
  obtain ⟨f, g, hfg, hlow⟩ := hd (‖d‖ / 3) (by linarith)
  have hsnd : ‖f * d * g‖ ≤ ‖d‖ / 3 := by
    refine le_trans (le_of_eq ?_) (le_trans (norm_snd_le _) hfg)
    change ‖f * d * g‖ = ‖f * (star (0 : ℂ) * 0) * g - f * d * g‖
    rw [mul_zero, mul_zero, zero_mul, zero_sub, norm_neg]
  linarith

end Detection

end XCVWitness
end GroupApproximation
