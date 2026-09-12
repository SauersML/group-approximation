import GroupApproximation.KOne.LeavittKOneScalarKernel
import GroupApproximation.Manuscript.OneSidedMFRadical.KhanhThanhDecompositionClosed
import GroupApproximation.Manuscript.NonMFSentences.LeavittMFQuotientSentences
import GroupApproximation.Manuscript.OneSidedMFRadical.MFQuotientUnitsKappaProof
import GroupApproximation.Meta.AxiomGuard

/-!
# `K₁(L_k(1,d)) ≅ k^×/(k^×)^{d-1}`, and the Leavitt corollary in full

`non_mf_groups_exist.tex`, `cor:leavitt-mf-quotient` (tex 1297–1304):

> Let `k` be a countable field, let `d ≥ 2`, let `R = L_k(1,d)`, and let `H = R^×`.
> Then `H ≅ GL_d(R)`, and under this identification `Rad_MF(H) = [H,H] = EL_d(R)` and
> `H/EL_d(R) ≅ K_1(R) ≅ k^×/(k^×)^{d-1}`.

and the introduction (tex 243–247):

> For a countable purely infinite simple ring `R` and `n ≥ 1`, Theorem
> `thm:mf-quotient-units` identifies `Rad_MF(GL_n(R))` with the commutator subgroup,
> and the largest MF quotient of `GL_n(R)` with `K_1(R)`.  For the unit group of
> `L_k(1,d)` the quotient is `k^×/(k^×)^{d-1}`.

The last isomorphism of the corollary is the combination of two theorems proved in
this repository with no literature input:

* `ScalarSurjective k d` (every `K₁`-class is a scalar class) ---
  `KhanhThanhDiagonal.scalarSurjective_holds`, from the arity-`d` elimination
  (`AryLeavitt.narrowReduction_holds`);
* `ScalarKernel k d` (a scalar killed in `K₁` is a `(d-1)`-st power) ---
  `LeavittKOneFormula.scalarKernel`, from the regularized determinant on the
  Toeplitz space of words.

## Endpoints

* `manuscriptLeavittKOneFormula` --- `K₁(L_k(1,d)) ≅ k^×/(k^×)^{d-1}` at every field
  and every `d ≥ 2`;
* `manuscriptSentence_quotientByElementaryIsScalarQuotient` --- the printed display
  `H/EL_d(R) ≅ k^×/(k^×)^{d-1}` through `K₁(R)`;
* `manuscriptLeavittMFQuotientFull` --- **every clause of `cor:leavitt-mf-quotient`**;
* `manuscriptSentence_unitGroupQuotient` --- tex 247: the largest MF quotient of the unit
  group of `L_k(1,d)` is `k^×/(k^×)^{d-1}`.
-/

namespace GroupApproximation
namespace LeavittKOneFormulaSentences

open AryLeavitt AlgebraicK Manuscript.OneSidedMFRadical MFQuotientUnits

/-- **`K₁(L_k(1,d)) ≅ k^×/(k^×)^{d-1}`**, at every field `k` and every `d ≥ 2`. -/
theorem leavittKOneFormula (k : Type) [Field k] (d : ℕ) (hd : 2 ≤ d) :
    Nonempty (AlgebraicKOne (AryLeavittAlgebra k d) ≃*
      (kˣ ⧸ LeavittKOneFormula.unitPowSubgroup k (d - 1))) :=
  LeavittKOneFormula.printedLeavittKOneFormula_of_scalarSurjective k d hd
    (KhanhThanhDiagonal.scalarSurjective_holds k d hd)

/-- The second isomorphism of `cor:leavitt-mf-quotient` at every field and every
`d ≥ 2`, as one closed proposition. -/
def PrintedLeavittKOneFormulaEveryArity : Prop :=
  ∀ (k : Type) [Field k] (d : ℕ), 2 ≤ d →
    Nonempty (AlgebraicKOne (AryLeavittAlgebra k d) ≃*
      (kˣ ⧸ LeavittKOneFormula.unitPowSubgroup k (d - 1)))

/-- **Closed endpoint**: `K₁(L_k(1,d)) ≅ k^×/(k^×)^{d-1}`. -/
theorem manuscriptLeavittKOneFormula : PrintedLeavittKOneFormulaEveryArity :=
  fun k _ d hd => leavittKOneFormula k d hd

/-- **The printed display `H/EL_d(R) ≅ K_1(R) ≅ k^×/(k^×)^{d-1}`**, composed through
`K₁(R)`.

> `H/EL_d(R) ≅ K_1(R) ≅ k^×/(k^×)^{d-1}`. (tex 1302) -/
theorem manuscriptSentence_quotientByElementaryIsScalarQuotient (k : Type) [Field k]
    [Countable k] (d : ℕ) (hd : 2 ≤ d) :
    letI : (elementaryGroup (Fin d) (AryLeavittAlgebra k d)).Normal :=
      LeavittMFQuotientSentences.elementaryGroup_normal k d hd
    Nonempty ((Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ ⧸
        elementaryGroup (Fin d) (AryLeavittAlgebra k d) ≃*
      (kˣ ⧸ LeavittKOneFormula.unitPowSubgroup k (d - 1))) :=
  letI : (elementaryGroup (Fin d) (AryLeavittAlgebra k d)).Normal :=
    LeavittMFQuotientSentences.elementaryGroup_normal k d hd
  ⟨(LeavittMFQuotientSentences.manuscriptSentence_quotientByElementaryIsKOne k d hd).some.trans
    (leavittKOneFormula k d hd).some⟩

/-- **`cor:leavitt-mf-quotient`, every clause.**

> Let `k` be a countable field, let `d ≥ 2`, let `R = L_k(1,d)`, and let `H = R^×`.
> Then `H ≅ GL_d(R)`, and under this identification `Rad_MF(H) = [H,H] = EL_d(R)` and
> `H/EL_d(R) ≅ K_1(R) ≅ k^×/(k^×)^{d-1}`. -/
def PrintedLeavittMFQuotientFull : Prop :=
  ∀ (k : Type) [Field k] [Countable k] (d : ℕ), 2 ≤ d →
    Nonempty ((AryLeavittAlgebra k d)ˣ ≃* (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ) ∧
      mfHomKernel (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ
          = commutator (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ ∧
      commutator (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ
          = elementaryGroup (Fin d) (AryLeavittAlgebra k d) ∧
      Nonempty ((Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ ⧸
          commutator (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ
        ≃* AlgebraicKOne (AryLeavittAlgebra k d)) ∧
      Nonempty (AlgebraicKOne (AryLeavittAlgebra k d) ≃*
        (kˣ ⧸ LeavittKOneFormula.unitPowSubgroup k (d - 1)))

/-- **Closed endpoint: `cor:leavitt-mf-quotient` in full.** -/
theorem manuscriptLeavittMFQuotientFull : PrintedLeavittMFQuotientFull := by
  intro k _ _ d hd
  obtain ⟨h1, h2, h3, h4⟩ :=
    LeavittMFQuotientSentences.manuscriptLeavittMFQuotientWithKOne k d hd
  exact ⟨h1, h2, h3, h4, leavittKOneFormula k d hd⟩

/-- **tex 247**: the largest MF quotient of the unit group of `L_k(1,d)` is
`k^×/(k^×)^{d-1}`.

> For the unit group of `L_k(1,d)` the quotient is `k^×/(k^×)^{d-1}`.

The quotient is the one of the preceding sentence, `H/Rad_MF(H) ≅ K₁(R)`
(`thm:mf-quotient-units` at `n = 1`, `MFQuotientUnitsKOne.manuscriptMFQuotientUnitsKOne`,
with pure infiniteness of `L_k(1,d)`), composed with `leavittKOneFormula`. -/
theorem manuscriptSentence_unitGroupQuotient (k : Type) [Field k] [Countable k] (d : ℕ)
    (hd : 2 ≤ d) :
    Nonempty ((AryLeavittAlgebra k d)ˣ ⧸ mfHomKernel (AryLeavittAlgebra k d)ˣ ≃*
      (kˣ ⧸ LeavittKOneFormula.unitPowSubgroup k (d - 1))) :=
  ⟨((MFQuotientUnitsKOne.manuscriptMFQuotientUnitsKOne (AryLeavittAlgebra k d)
      (LeavittMFQuotientSentences.isPurelyInfiniteSimpleRing_aryLeavitt k d hd)).2.2.2).some.trans
    (leavittKOneFormula k d hd).some⟩

end LeavittKOneFormulaSentences
end GroupApproximation

/-! ### Axiom audit -/

#audit_closed_axioms GroupApproximation.LeavittKOneFormulaSentences.manuscriptLeavittKOneFormula
#audit_closed_axioms GroupApproximation.LeavittKOneFormulaSentences.manuscriptLeavittMFQuotientFull
#audit_axioms GroupApproximation.LeavittKOneFormulaSentences.leavittKOneFormula
#audit_axioms
  GroupApproximation.LeavittKOneFormulaSentences.manuscriptSentence_quotientByElementaryIsScalarQuotient
#audit_axioms GroupApproximation.LeavittKOneFormulaSentences.manuscriptSentence_unitGroupQuotient
