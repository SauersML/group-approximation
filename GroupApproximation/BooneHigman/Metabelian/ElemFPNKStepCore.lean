import GroupApproximation.BooneHigman.Metabelian.ElemFPNilFGPosTeleEndpoint
import GroupApproximation.BooneHigman.Metabelian.ElemFPZInvK2Trivial
import GroupApproximation.Meta.AxiomGuard

/-!
# The `NK₂` step over `ℤ[1/m][x₁, …, x_j]`: peeling off `m = 0` (lane bh-met-95d)

The target `ElemFPNilFGPosTele.CharZeroK2NilStepFGDiagStatement` says that for every `m, j` the
kernel of `K₂(j+5, B[t]) → K₂(j+5, B)`, `t ↦ 0`, is finitely generated, where
`B = ℤ[1/m][x₁, …, x_j]`.

## Truth check (LOUD)

The target is **true**, but the argument is deep.  The kernel is in fact trivial:

* for `m ≠ 0`, `B` is regular Noetherian, so Quillen gives `NK₂(B) = 0`;
* `sr(B[t]) ≤ j + 3`, so van der Kallen's injective stability puts rank `j + 5` in the
  stable range.

Neither input is in the corpus, and both are literature inputs.  So **the target is NOT
closed here.**

## What this file proves

* The degenerate instance `m = 0` holds unconditionally.  There `ℤ[1/0]` is the zero ring, so
  every `K₂` is trivial (`nkStep_stepFG_zero`).
* The residual `nkStep_StepFGPosStatement` is the target restricted to `0 < m`, and
  `nkStep_stepFGDiag_of_StepFGPos` reduces the target to it.
* `nkStep_charZeroK2NilFGPos_of_StepFGPos` gives the downstream `CharZeroK2NilFGPosStatement`.

## Strength of the residual (LOUD)

The residual is a restriction of the target, so the target trivially implies it
(`nkStep_StepFGPos_of_stepFGDiag`).  It is strictly smaller in *proof content* only by the
degenerate `m = 0` case proved here.  Modulo that proved instance it is **logically
equivalent** to the target.  All of the real content (Quillen plus injective stability) is
still in the residual.  It is not equivalent to `CharZeroK2NilPosStatement` or to any
`PolyK2StabRangeDiag`-type statement.  It avoids the Karoubi, lattice-height and SuslinCongVac
routes.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPNKStep

open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.BooneHigman.Metabelian.ElemFP
open GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
open GroupApproximation.BooneHigman.Metabelian.ElemFPNilFGPosTele

/-- Over a zero ring `A`, the kernel of `K₂(I, A[t]) → K₂(I, A)` at `t = 0` is finitely
generated. It is in fact trivial. -/
theorem nkStep_evalZero_ker_fg_of_subsingleton (A : Type*) [CommRing A] [Subsingleton A]
    (I : Type*) [Fintype I] [DecidableEq I] :
    Group.FG (K2Map (I := I) (Polynomial.evalRingHom 0 : Polynomial A →+* A)).ker := by
  have hP : Subsingleton (Polynomial A) :=
    RingHom.codomain_trivial (Polynomial.C : A →+* Polynomial A)
  have hker : (K2Map (I := I) (Polynomial.evalRingHom 0 : Polynomial A →+* A)).ker = ⊥ :=
    (Subgroup.eq_bot_iff_forall _).mpr fun u _ ↦ k2_eq_one_of_subsingleton u
  rw [Group.fg_iff_subgroup_fg, hker]
  exact Subgroup.FG.bot

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPNKStep.nkStep_evalZero_ker_fg_of_subsingleton

/-- The degenerate instance `m = 0` of the step statement.  `ℤ[1/0]` is the zero ring. -/
theorem nkStep_stepFG_zero (j : ℕ) : Group.FG (K2Map (I := Fin (j + 5))
    (Polynomial.evalRingHom 0 :
      Polynomial (MvPolynomial (Fin j) (Localization.Away ((0 : ℕ) : ℤ))) →+*
        MvPolynomial (Fin j) (Localization.Away ((0 : ℕ) : ℤ)))).ker := by
  have hs : Subsingleton (Localization.Away ((0 : ℕ) : ℤ)) :=
    localizationAway_subsingleton_of_eq_zero Nat.cast_zero
  have hS : Subsingleton (MvPolynomial (Fin j) (Localization.Away ((0 : ℕ) : ℤ))) :=
    RingHom.codomain_trivial (MvPolynomial.C : Localization.Away ((0 : ℕ) : ℤ) →+*
      MvPolynomial (Fin j) (Localization.Away ((0 : ℕ) : ℤ)))
  exact nkStep_evalZero_ker_fg_of_subsingleton _ _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPNKStep.nkStep_stepFG_zero

/-- **Residual.**  The step statement `CharZeroK2NilStepFGDiagStatement` restricted to
`0 < m`, which excludes the degenerate zero-ring case.  It is true by Quillen's `NK₂(B) = 0`
for the regular ring `B = ℤ[1/m][x₁, …, x_j]` together with injective stability in rank
`j + 5`.  See the module docstring for its strength. -/
def nkStep_StepFGPosStatement : Prop :=
  ∀ m j : ℕ, 0 < m → Group.FG (K2Map (I := Fin (j + 5))
    (Polynomial.evalRingHom 0 :
      Polynomial (MvPolynomial (Fin j) (Localization.Away (m : ℤ))) →+*
        MvPolynomial (Fin j) (Localization.Away (m : ℤ)))).ker

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPNKStep.nkStep_StepFGPosStatement

/-- The residual implies the target step statement.  The instance `m = 0` is discharged
unconditionally. -/
theorem nkStep_stepFGDiag_of_StepFGPos (h : nkStep_StepFGPosStatement) :
    CharZeroK2NilStepFGDiagStatement := by
  intro m j
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact nkStep_stepFG_zero j
  · exact h m j hm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPNKStep.nkStep_stepFGDiag_of_StepFGPos

/-- The converse, which is trivial: the residual is a restriction of the target. -/
theorem nkStep_StepFGPos_of_stepFGDiag (h : CharZeroK2NilStepFGDiagStatement) :
    nkStep_StepFGPosStatement :=
  fun m j _ ↦ h m j

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPNKStep.nkStep_StepFGPos_of_stepFGDiag

/-- Downstream endpoint: the residual gives `CharZeroK2NilFGPosStatement`. -/
theorem nkStep_charZeroK2NilFGPos_of_StepFGPos (h : nkStep_StepFGPosStatement) :
    CharZeroK2NilFGPosStatement :=
  charZeroK2NilFGPos_of_stepFGDiag (nkStep_stepFGDiag_of_StepFGPos h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPNKStep.nkStep_charZeroK2NilFGPos_of_StepFGPos

end GroupApproximation.BooneHigman.Metabelian.ElemFPNKStep
