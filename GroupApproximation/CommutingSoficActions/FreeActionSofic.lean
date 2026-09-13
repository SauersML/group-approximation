import GroupApproximation.Algebra.DiagonalCosetAction
import GroupApproximation.Sofic.SoficActionOrbits
import Mathlib.GroupTheory.ResiduallyFinite

/-!
# Free actions of residually finite groups are sofic

Every point stabilizer of a free action is trivial.  In a residually finite
group every element outside the trivial subgroup avoids some finite-index
subgroup, so each stabilizer coset action is sofic
(`isSoficAction_quotient_of_separable`), and gluing the orbits
(`isSoficAction_of_stabilizers`, Proposition 2.16 of Gao–Kunnawalkam
Elayavalli–Patchell, arXiv:2401.04945v3) makes the action sofic.

On `(G × G) ⧸ ΔH` both coordinate actions of `G` are free for every subgroup
`H` (`DiagonalCosetAction.eq_one_of_fst_smul_fixed`,
`DiagonalCosetAction.eq_one_of_snd_smul_fixed`), so both are sofic once `G` is
residually finite.
-/

namespace GroupApproximation.CommutingSoficActions

open DiagonalCosetAction

universe u

variable {G : Type u} [Group G]

/-- A free action of a residually finite group is sofic. -/
theorem isSoficAction_of_free [Group.ResiduallyFinite G] {X : Type u} [MulAction G X]
    (hfree : ∀ (g : G) (x : X), g • x = x → g = 1) : IsSoficAction G X := by
  refine isSoficAction_of_stabilizers fun x => ?_
  refine isSoficAction_quotient_of_separable _ fun g hg => ?_
  have hg1 : g ≠ 1 := by
    rintro rfl
    exact hg (MulAction.stabilizer G x).one_mem
  obtain ⟨K, hK, hgK⟩ :=
    Group.residuallyFinite_iff_exists_finiteIndex.mp ‹Group.ResiduallyFinite G› g hg1
  refine ⟨K, fun a ha => ?_, hK, hgK⟩
  rw [hfree a x (MulAction.mem_stabilizer_iff.mp ha)]
  exact K.one_mem

variable (H : Subgroup G)

/-- The first coordinate action `g · (a, b)ΔH = (ga, b)ΔH` is sofic. -/
theorem isSoficAction_diagonalCosets_inl [Group.ResiduallyFinite G] :
    @IsSoficAction G _ ((G × G) ⧸ diagSubgroup H)
      (MulAction.compHom _ (MonoidHom.inl G G)) := by
  letI : MulAction G ((G × G) ⧸ diagSubgroup H) :=
    MulAction.compHom _ (MonoidHom.inl G G)
  exact isSoficAction_of_free fun g x hx => eq_one_of_fst_smul_fixed H hx

/-- The second coordinate action `g · (a, b)ΔH = (a, gb)ΔH` is sofic. -/
theorem isSoficAction_diagonalCosets_inr [Group.ResiduallyFinite G] :
    @IsSoficAction G _ ((G × G) ⧸ diagSubgroup H)
      (MulAction.compHom _ (MonoidHom.inr G G)) := by
  letI : MulAction G ((G × G) ⧸ diagSubgroup H) :=
    MulAction.compHom _ (MonoidHom.inr G G)
  exact isSoficAction_of_free fun g x hx => eq_one_of_snd_smul_fixed H hx

end GroupApproximation.CommutingSoficActions
