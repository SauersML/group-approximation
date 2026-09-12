import GroupApproximation.Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit

/-!
# Density of represented group generators

The trace proof needs the elementary fact that a C-star algebra defined as
`C*(ρ(G))` is the closed linear span of the represented unitaries.
-/

namespace GroupApproximation
namespace HNNTrace

open GroupApproximation.Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit
open scoped Pointwise

noncomputable section

universe u v

variable {G : Type u} [Group G] {A : Type v} [CStarAlgebra A]

/-- The represented unitaries, regarded as an ambient-algebra monoid map. -/
def representedAmbientHom (rho : G →* unitary A) : G →* A :=
  (unitary A).subtype.comp rho

@[simp] theorem representedAmbientHom_apply (rho : G →* unitary A) (g : G) :
    representedAmbientHom rho g = ((rho g : unitary A) : A) :=
  rfl

theorem star_representedAmbientHom (rho : G →* unitary A) (g : G) :
    star (representedAmbientHom rho g) = representedAmbientHom rho g⁻¹ := by
  have hright : representedAmbientHom rho g *
      star (representedAmbientHom rho g) = 1 := (rho g).property.2
  have hleft : representedAmbientHom rho g⁻¹ *
      representedAmbientHom rho g = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  calc
    star (representedAmbientHom rho g) =
        representedAmbientHom rho g⁻¹ * representedAmbientHom rho g *
          star (representedAmbientHom rho g) := by rw [hleft, one_mul]
    _ = representedAmbientHom rho g⁻¹ *
          (representedAmbientHom rho g * star (representedAmbientHom rho g)) := by
            rw [mul_assoc]
    _ = representedAmbientHom rho g⁻¹ := by rw [hright, mul_one]

/-- The generated star algebra is contained in the linear span of the group
unitaries: multiplication and star introduce no new monomials. -/
theorem represented_adjoin_le_span (rho : G →* unitary A) :
    (StarAlgebra.adjoin ℂ
        (Set.range ⇑(representedAmbientHom rho))).toSubalgebra.toSubmodule ≤
      Submodule.span ℂ (Set.range ⇑(representedAmbientHom rho)) := by
  rw [StarAlgebra.adjoin_eq_span]
  apply Submodule.span_mono
  have hle : Submonoid.closure
      (Set.range ⇑(representedAmbientHom rho) ∪
        star (Set.range ⇑(representedAmbientHom rho))) ≤
      MonoidHom.mrange (representedAmbientHom rho) := by
    apply Submonoid.closure_le.mpr
    rintro x (⟨g, rfl⟩ | hx)
    · exact ⟨g, rfl⟩
    · rw [← Set.image_star] at hx
      obtain ⟨y, ⟨g, rfl⟩, rfl⟩ := hx
      exact ⟨g⁻¹, (star_representedAmbientHom rho g).symm⟩
  intro x hx
  exact hle hx

/-- The span of the canonical generators is dense in `C*(ρ(G))`. -/
theorem groupGeneratedCStar_dense_span (rho : G →* unitary A) :
    Dense (Submodule.span ℂ
      (Set.range (fun g : G ↦
        ((groupGeneratedUnitaryHom rho g : unitary (groupGeneratedCStar rho)) :
          groupGeneratedCStar rho))) : Set (groupGeneratedCStar rho)) := by
  have himg : ∀ y ∈ Submodule.span ℂ
      (Set.range ⇑(representedAmbientHom rho)),
      y ∈ Subtype.val ''
        (Submodule.span ℂ
          (Set.range (fun g : G ↦
            ((groupGeneratedUnitaryHom rho g :
              unitary (groupGeneratedCStar rho)) : groupGeneratedCStar rho))) :
          Set (groupGeneratedCStar rho)) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨g, rfl⟩ := hx
        exact ⟨_, Submodule.subset_span ⟨g, rfl⟩, rfl⟩
    | zero => exact ⟨0, Submodule.zero_mem _, rfl⟩
    | add x y _ _ hx hy =>
        obtain ⟨a, ha, rfl⟩ := hx
        obtain ⟨b, hb, rfl⟩ := hy
        exact ⟨a + b, Submodule.add_mem _ ha hb, rfl⟩
    | smul c x _ hx =>
        obtain ⟨a, ha, rfl⟩ := hx
        exact ⟨c • a, Submodule.smul_mem _ c ha, rfl⟩
  refine (Subtype.dense_iff (s := (groupGeneratedCStar rho : Set A))).mpr ?_
  intro y hy
  have hy' : y ∈ closure
      ((StarAlgebra.adjoin ℂ (Set.range ⇑(representedAmbientHom rho)) :
        StarSubalgebra ℂ A) : Set A) := by
    rw [← StarSubalgebra.topologicalClosure_coe]
    exact hy
  refine closure_mono ?_ hy'
  intro z hz
  exact himg z (represented_adjoin_le_span rho hz)

end

end HNNTrace
end GroupApproximation
