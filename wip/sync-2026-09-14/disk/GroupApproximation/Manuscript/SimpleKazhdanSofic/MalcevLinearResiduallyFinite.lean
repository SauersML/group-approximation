import GroupApproximation.Algebra.MalcevLinear
import GroupApproximation.Dynamics.SurjunctivityTransfer
import GroupApproximation.Meta.AxiomGuard

/-!
# Malcev's theorem as printed in the simple Kazhdan note

`simple_kazhdan_sofic_group.tex` at 9047d0d3c, l.352–353, in the proof of the second corollary
of "LEF groups": "Finitely generated linear groups are residually finite by Malcev's theorem".

A linear group is a group with a faithful finite-dimensional representation over a field, that
is, an injective homomorphism into `GL_d(F)` for some `d` and some field `F`.  The proof is the
repository's Mal'cev theorem `MalcevLinear.residuallyFinite_of_fg`:
* the entries of a finite generating set and of their inverses generate a finitely generated
  subring `R` of `F`, and the group lies in `GL_d(R)`;
* a nonzero entry of `g - 1` survives in a finite residue field of `R`
  (`exists_finite_field_hom_of_ne_zero`, over the Jacobson property of `ℤ`).
No literature input.
-/

namespace GroupApproximation

namespace SimpleKazhdanSofic

universe u v

/-- Tex l.352–353: finitely generated linear groups are residually finite. -/
def PrintedFGLinearResiduallyFinite : Prop :=
  ∀ (G : Type u) [Group G] [Group.FG G] (d : ℕ) (F : Type v) [Field F]
    (ρ : G →* Matrix.GeneralLinearGroup (Fin d) F), Function.Injective ρ →
      Group.ResiduallyFinite G

theorem printedFGLinearResiduallyFinite : PrintedFGLinearResiduallyFinite.{u, v} := by
  intro G _ _ d F _ ρ hρ
  by_contra h
  exact MalcevLinear.not_injective_of_not_residuallyFinite h ρ hρ

/-- The same sentence with the repository's residual finiteness `IsResiduallyFinite`. -/
def PrintedFGLinearIsResiduallyFinite : Prop :=
  ∀ (G : Type u) [Group G] [Group.FG G] (d : ℕ) (F : Type v) [Field F]
    (ρ : G →* Matrix.GeneralLinearGroup (Fin d) F), Function.Injective ρ →
      IsResiduallyFinite G

theorem fgLinear_isResiduallyFinite : PrintedFGLinearIsResiduallyFinite.{u, v} := by
  intro G _ _ d F _ ρ hρ
  exact isResiduallyFinite_iff_group_residuallyFinite.mpr
    ((printedFGLinearResiduallyFinite.{u, v}) G d F ρ hρ)

end SimpleKazhdanSofic

end GroupApproximation

#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedFGLinearResiduallyFinite
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.fgLinear_isResiduallyFinite
