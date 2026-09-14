import GroupApproximation.Dynamics.SurjunctivitySubgroup
import GroupApproximation.Dynamics.SurjunctivityResiduallyFinite
import Mathlib.GroupTheory.ResiduallyFinite

/-! # Transport of surjunctivity and the residual-finiteness interface -/

namespace GroupApproximation

universe u v w

variable {G : Type u} [Group G] {H : Type v} [Group H]

/-- The repository and Mathlib definitions of residual finiteness agree. -/
theorem isResiduallyFinite_iff_group_residuallyFinite :
    IsResiduallyFinite G ↔ Group.ResiduallyFinite G :=
  isResiduallyFinite_iff.trans Group.residuallyFinite_iff_exists_finiteIndex.symm

namespace Surjunctivity

/-- Transport surjunctivity across an isomorphism of groups. -/
theorem IsSurjunctive.of_mulEquiv (hH : IsSurjunctive H) (e : G ≃* H) :
    IsSurjunctive G := by
  intro B _ _ _ τ hcont heq hinj
  let T : (H → B) → (H → B) := fun y h => τ (fun g => y (e g)) (e.symm h)
  have hTcont : Continuous T := by
    apply continuous_pi
    intro h
    exact (continuous_apply (e.symm h)).comp
      (hcont.comp (continuous_pi fun g => continuous_apply (e g)))
  have hTeq : IsEquivariant T := by
    intro k y
    funext h
    have hin : (fun g => (shift k y) (e g)) =
        shift (e.symm k) (fun g => y (e g)) := by
      funext g
      simp only [shift, map_mul, e.apply_symm_apply]
    change τ (fun g => (shift k y) (e g)) (e.symm h) =
      τ (fun g => y (e g)) (e.symm (k * h))
    rw [hin, heq]
    simp only [shift, map_mul]
  have hTinj : Function.Injective T := by
    intro x y hxy
    have hτ : τ (fun g => x (e g)) = τ (fun g => y (e g)) := by
      funext g
      have h := congrFun hxy (e g)
      simpa only [T, e.symm_apply_apply] using h
    have h := hinj hτ
    funext k
    simpa only [e.apply_symm_apply] using congrFun h (e.symm k)
  intro y
  obtain ⟨z, hz⟩ := hH B T hTcont hTeq hTinj (fun h => y (e.symm h))
  refine ⟨fun g => z (e g), ?_⟩
  funext g
  simpa only [T, e.symm_apply_apply] using congrFun hz (e g)

theorem isSurjunctive_mulEquiv_iff (e : G ≃* H) :
    IsSurjunctive G ↔ IsSurjunctive H :=
  ⟨fun hG => hG.of_mulEquiv e.symm, fun hH => hH.of_mulEquiv e⟩

/-- Surjunctivity pulls back along an injective group homomorphism. -/
theorem IsSurjunctive.of_injective (hH : IsSurjunctive H) (f : G →* H)
    (hf : Function.Injective f) : IsSurjunctive G := by
  let e : G ≃* f.range := MulEquiv.ofBijective f.rangeRestrict
    ⟨fun _ _ h => hf (congrArg Subtype.val h), by
      intro y
      obtain ⟨x, hx⟩ := y.property
      exact ⟨x, Subtype.ext hx⟩⟩
  exact (hH.subgroup f.range).of_mulEquiv e

/-- Mathlib's residual-finiteness class implies surjunctivity. -/
theorem isSurjunctive_of_residuallyFinite [Group.ResiduallyFinite G] :
    IsSurjunctive G :=
  isSurjunctive_of_isResiduallyFinite
    (isResiduallyFinite_iff_group_residuallyFinite.mpr inferInstance)

end Surjunctivity
end GroupApproximation
