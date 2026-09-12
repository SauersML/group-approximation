import GroupApproximation.Higman.TransportStarCode
import GroupApproximation.Computability.BenignComapCodeSemantics
import GroupApproximation.Computability.BenignSupCodeSemantics

/-!
# Marked semantics of the effective TransportStar output

The last TransportStar operation is a three-mark preimage.  Consequently its
emitted `RankThreeInputData` has a direct-product ambient, the full left factor
and the transported right cutter as cutter, and three literal diagonal marked
words.  This file states those facts both syntactically and under the concrete
product-code equivalence.
-/

namespace GroupApproximation
namespace Higman
namespace TransportStarCodeSemantics

open PresentationCodes
open TransportStarCode MikhailovaRopeCode
open BenignInfCode BenignInfCodeSemantics

private noncomputable abbrev finalInput
    (x : TransportStarCode.Input) : BenignInfCode.Input :=
  (freeRankThreeSyntax, finalRightSyntax x)

@[simp] theorem rankThreeData_ambient (x : TransportStarCode.Input) :
    (rankThreeData x).1 =
      DirectProductCode.productCode (presentationSkeleton 2) (hjoin x).1 := rfl

@[simp] theorem rankThreeData_cutting (x : TransportStarCode.Input) :
    (rankThreeData x).2.1 =
      BenignSupCode.leftGeneratorWords (finalInput x) ++
        BenignInfCode.rightCuttingWords (finalInput x) := rfl

@[simp] theorem rankThreeData_word_zero (x : TransportStarCode.Input) :
    (rankThreeData x).2.2.1 = BenignInfCode.diagonalAt (finalInput x) 0 := rfl

@[simp] theorem rankThreeData_word_one (x : TransportStarCode.Input) :
    (rankThreeData x).2.2.2.1 = BenignInfCode.diagonalAt (finalInput x) 1 := rfl

@[simp] theorem rankThreeData_word_two (x : TransportStarCode.Input) :
    (rankThreeData x).2.2.2.2 = BenignInfCode.diagonalAt (finalInput x) 2 := rfl

/-- The first final marked word is the pair of the first free generator and
the fourth mark of the two-HNN join witness. -/
theorem productCodeEquiv_word_zero (x : TransportStarCode.Input) :
    DirectProductCodeSemantics.productCodeEquiv
        (presentationSkeleton 2) (hjoin x).1
        (evalWord (rankThreeData x).1 (rankThreeData x).2.2.1) =
      (evalWord (presentationSkeleton 2) (rankThreeGeneratorWord 0),
        evalWord (hjoin x).1 ((hjoin x).2.2.getD 3 [])) := by
  change DirectProductCodeSemantics.productCodeEquiv
      (BenignInfCode.leftCode (finalInput x))
      (BenignInfCode.rightCode (finalInput x))
      (evalWord (BenignComapThreeCode.transform (finalInput x)).1
        (BenignInfCode.diagonalAt (finalInput x) 0)) = _
  exact BenignComapCodeSemantics.productCodeEquiv_threeMark
    (finalInput x) ⟨0, by omega⟩

/-- The second final marked word is the pair of the second free generator and
the fifth mark of the two-HNN join witness. -/
theorem productCodeEquiv_word_one (x : TransportStarCode.Input) :
    DirectProductCodeSemantics.productCodeEquiv
        (presentationSkeleton 2) (hjoin x).1
        (evalWord (rankThreeData x).1 (rankThreeData x).2.2.2.1) =
      (evalWord (presentationSkeleton 2) (rankThreeGeneratorWord 1),
        evalWord (hjoin x).1 ((hjoin x).2.2.getD 4 [])) := by
  change DirectProductCodeSemantics.productCodeEquiv
      (BenignInfCode.leftCode (finalInput x))
      (BenignInfCode.rightCode (finalInput x))
      (evalWord (BenignComapThreeCode.transform (finalInput x)).1
        (BenignInfCode.diagonalAt (finalInput x) 1)) = _
  exact BenignComapCodeSemantics.productCodeEquiv_threeMark
    (finalInput x) ⟨1, by omega⟩

/-- The third final marked word is the pair of the third free generator and
the sixth mark of the two-HNN join witness. -/
theorem productCodeEquiv_word_two (x : TransportStarCode.Input) :
    DirectProductCodeSemantics.productCodeEquiv
        (presentationSkeleton 2) (hjoin x).1
        (evalWord (rankThreeData x).1 (rankThreeData x).2.2.2.2) =
      (evalWord (presentationSkeleton 2) (rankThreeGeneratorWord 2),
        evalWord (hjoin x).1 ((hjoin x).2.2.getD 5 [])) := by
  change DirectProductCodeSemantics.productCodeEquiv
      (BenignInfCode.leftCode (finalInput x))
      (BenignInfCode.rightCode (finalInput x))
      (evalWord (BenignComapThreeCode.transform (finalInput x)).1
        (BenignInfCode.diagonalAt (finalInput x) 2)) = _
  exact BenignComapCodeSemantics.productCodeEquiv_threeMark
    (finalInput x) ⟨2, by omega⟩

end TransportStarCodeSemantics
end Higman
end GroupApproximation
