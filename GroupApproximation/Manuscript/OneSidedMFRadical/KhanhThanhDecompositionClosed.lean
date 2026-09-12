import GroupApproximation.Manuscript.OneSidedMFRadical.KhanhThanhDecompositionResidual
import GroupApproximation.KOne.AryRefineLoopDischarge
import GroupApproximation.Meta.AxiomGuard

/-!
# `GL_d(R) = EL_d(R) D_d(k)`, closed

`non_mf_groups_exist.tex`, proof of `cor:leavitt-mf-quotient`:

> Khanh--Thanh show that `GL_d(R) = EL_d(R)D_d(k)`, where `D_d(k)` is the abelian
> group of diagonal matrices with entries in `k^×`, which normalizes `EL_d(R)` ...
> So `[H,H] ≤ EL_d(R)`

for `R = L_k(1,d)`, every field `k` and every `d ≥ 2`, with no literature input.
`KhanhThanhDecompositionResidual.lean` reduces the decomposition to
`AryLeavitt.NarrowReduction k d`, and `KOne/AryRefineLoopDischarge.lean` proves that
proposition outright (`AryLeavitt.narrowReduction_holds`).  So the printed decomposition,
its spelling consumed by `KOne/LeavittKOneScalarSurjectivity.lean`, `K₁`-surjectivity of the
scalars, and the printed consequence `[H,H] ≤ EL_d(R)` all hold unconditionally.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace KhanhThanhDiagonal

open AryLeavitt RankNElimination MatrixDiagonalization

variable (k : Type) [Field k] (d : ℕ)

/-- **Khanh--Thanh's decomposition `GL_d(R) = EL_d(R) D_d(k)`**, at every field and every
`d ≥ 2`. -/
theorem printedKhanhThanhDecomposition_holds (hd : 2 ≤ d) :
    PrintedKhanhThanhDecomposition k d :=
  printedKhanhThanhDecomposition_of_narrowReduction k d hd (narrowReduction_holds k d hd)

/-- The decomposition in the spelling `KOne/LeavittKOneScalarSurjectivity.lean` consumes. -/
theorem printedKhanhThanhDiagonalDecomposition_holds (hd : 2 ≤ d) :
    LeavittKOneScalar.PrintedKhanhThanhDiagonalDecomposition k d :=
  printedKhanhThanhDiagonalDecomposition_of_narrowReduction k d hd (narrowReduction_holds k d hd)

/-- Every class of `K₁(L_k(1,d))` is the class of a scalar. -/
theorem scalarSurjective_holds (hd : 2 ≤ d) : LeavittKOneFormula.ScalarSurjective k d :=
  scalarSurjective_of_scalarReduction_ary k d hd (scalarReduction_holds k d hd)

/-- **"So `[H,H] ≤ EL_d(R)`"**, along the printed route, unconditionally. -/
theorem commutator_le_elementaryGroup_printed (hd : 2 ≤ d) :
    commutator (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ ≤
      elementaryGroup (Fin d) (AryLeavittAlgebra k d) :=
  commutator_le_elementaryGroup_of_printedDecomposition k d hd
    (printedKhanhThanhDecomposition_holds k d hd)

/-- The printed decomposition `GL_d(L_k(1,d)) = EL_d D_d(k)` at every field and every
`d ≥ 2`, as one closed proposition. -/
def PrintedKhanhThanhDecompositionEveryArity : Prop :=
  ∀ (k : Type) [Field k] (d : ℕ), 2 ≤ d → PrintedKhanhThanhDecomposition k d

/-- `K₁`-surjectivity of the scalars of `L_k(1,d)` at every field and every `d ≥ 2`, as one
closed proposition. -/
def ScalarSurjectiveEveryArity : Prop :=
  ∀ (k : Type) [Field k] (d : ℕ), 2 ≤ d → LeavittKOneFormula.ScalarSurjective k d

/-- **Closed endpoint**: the printed Khanh--Thanh decomposition. -/
theorem printedKhanhThanhDecomposition_everyArity : PrintedKhanhThanhDecompositionEveryArity :=
  fun k _ d hd ↦ printedKhanhThanhDecomposition_holds k d hd

/-- **Closed endpoint**: every `K₁`-class of `L_k(1,d)` is a scalar class. -/
theorem scalarSurjective_everyArity : ScalarSurjectiveEveryArity :=
  fun k _ d hd ↦ scalarSurjective_holds k d hd

/-- "So `[H,H] ≤ EL_d(R)`" at every field and every `d ≥ 2`, as one closed proposition. -/
def CommutatorInElementaryPrintedEveryArity : Prop :=
  ∀ (k : Type) [Field k] (d : ℕ), 2 ≤ d →
    commutator (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ ≤
      elementaryGroup (Fin d) (AryLeavittAlgebra k d)

/-- **Closed carrier of the printed consequence** "So `[H,H] ≤ EL_d(R)`": the printed-route
lemma instantiated with the closed decomposition. -/
theorem manuscriptSentence_commutatorInElementaryPrinted :
    CommutatorInElementaryPrintedEveryArity :=
  fun k _ d hd ↦ commutator_le_elementaryGroup_of_printedDecomposition k d hd
    (printedKhanhThanhDecomposition_everyArity k d hd)

end KhanhThanhDiagonal
end OneSidedMFRadical
end Manuscript
end GroupApproximation

/-! ### Axiom audit -/

#audit_closed_axioms
  GroupApproximation.Manuscript.OneSidedMFRadical.KhanhThanhDiagonal.printedKhanhThanhDecomposition_everyArity
#audit_closed_axioms
  GroupApproximation.Manuscript.OneSidedMFRadical.KhanhThanhDiagonal.scalarSurjective_everyArity

#audit_axioms
  GroupApproximation.Manuscript.OneSidedMFRadical.KhanhThanhDiagonal.printedKhanhThanhDecomposition_holds
#audit_axioms
  GroupApproximation.Manuscript.OneSidedMFRadical.KhanhThanhDiagonal.printedKhanhThanhDiagonalDecomposition_holds
#audit_axioms
  GroupApproximation.Manuscript.OneSidedMFRadical.KhanhThanhDiagonal.scalarSurjective_holds
#audit_axioms
  GroupApproximation.Manuscript.OneSidedMFRadical.KhanhThanhDiagonal.commutator_le_elementaryGroup_printed
