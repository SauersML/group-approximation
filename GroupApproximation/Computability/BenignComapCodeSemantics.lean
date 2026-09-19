import GroupApproximation.Computability.BenignComapThreeCode
import GroupApproximation.Computability.BenignInfCodeSemantics

/-!
# Semantics of the effective benign-preimage syntax

The computed preimage witness uses the product ambient.  Its cutter contains
every left presentation generator and the old right cutter, while its marked
words are diagonal pairs.  These formulas identify those literal raw words
under the concrete product-code equivalence.
-/

namespace GroupApproximation
namespace BenignComapCodeSemantics

open PresentationCodes
open BenignInfCode BenignInfCodeSemantics

/-- The raw one-letter word emitted by `generatorWords` evaluates to the
corresponding numbered generator. -/
theorem evalWord_generatorWord (c : PresentationCode) (i : ℕ) :
    evalWord c [(i, true)] = PresentedGroup.of (letterOf c i) := by
  change PresentedGroup.mk (DirectProductCodeSemantics.codeRels c)
      (FreeGroup.mk [(letterOf c i, true)]) =
    PresentedGroup.mk (DirectProductCodeSemantics.codeRels c)
      (FreeGroup.of (letterOf c i))
  rfl

/-- Each left generator word inserted in the computed preimage cutter lands
in the left factor as the corresponding coded generator. -/
theorem productCodeEquiv_leftGeneratorWord
    (x : Input) (i : Fin (genCount (leftCode x))) :
    DirectProductCodeSemantics.productCodeEquiv (leftCode x) (rightCode x)
        (evalWord (BenignComapCode.transform x).1
          (DirectProductCode.leftWord (leftCode x) [(i, true)])) =
      ((PresentedGroup.of i, 1) : Carrier (leftCode x) × Carrier (rightCode x)) := by
  change DirectProductCodeSemantics.productCodeEquiv (leftCode x) (rightCode x)
      (evalWord (DirectProductCode.productCode (leftCode x) (rightCode x))
        (DirectProductCode.leftWord (leftCode x) [(i, true)])) = _
  rw [productCodeEquiv_eval_leftWord, evalWord_generatorWord]
  have hi : letterOf (leftCode x) (i : ℕ) = i := by
    apply Fin.ext
    exact RawWord.letterOf_val_of_lt (leftCode x) i.isLt
  rw [hi]

/-- The six-mark preimage transform evaluates every computed mark to the
corresponding diagonal pair. -/
theorem productCodeEquiv_mark (x : Input) (i : ℕ) :
    DirectProductCodeSemantics.productCodeEquiv (leftCode x) (rightCode x)
        (evalWord (BenignComapCode.transform x).1 (diagonalAt x i)) =
      (evalWord (leftCode x) ((leftMarks x).getD i []),
        evalWord (rightCode x) ((rightMarks x).getD i [])) := by
  change DirectProductCodeSemantics.productCodeEquiv (leftCode x) (rightCode x)
      (evalWord (DirectProductCode.productCode (leftCode x) (rightCode x))
        (diagonalAt x i)) = _
  exact productCodeEquiv_diagonalAt x i

/-- The three-mark specialization has exactly the same diagonal semantics. -/
theorem productCodeEquiv_threeMark (x : Input) (i : Fin 3) :
    DirectProductCodeSemantics.productCodeEquiv (leftCode x) (rightCode x)
        (evalWord (BenignComapThreeCode.transform x).1 (diagonalAt x i)) =
      (evalWord (leftCode x) ((leftMarks x).getD i []),
        evalWord (rightCode x) ((rightMarks x).getD i [])) := by
  change DirectProductCodeSemantics.productCodeEquiv (leftCode x) (rightCode x)
      (evalWord (DirectProductCode.productCode (leftCode x) (rightCode x))
        (diagonalAt x (i : ℕ))) = _
  exact productCodeEquiv_diagonalAt x i

/-- Every old right cutter word occurs in the computed preimage cutter and
evaluates in the right factor. -/
theorem exists_rightCutterWord (x : Input) {w : Raw}
    (hw : w ∈ rightCutter x) :
    ∃ u ∈ (BenignComapCode.transform x).2.1,
      DirectProductCodeSemantics.productCodeEquiv (leftCode x) (rightCode x)
          (evalWord (BenignComapCode.transform x).1 u) =
        ((1, evalWord (rightCode x) w) : Carrier (leftCode x) ×
          Carrier (rightCode x)) := by
  obtain ⟨u, hu, heval⟩ := exists_rightCuttingWord x hw
  refine ⟨u, ?_, ?_⟩
  · exact List.mem_append_right _ hu
  · change DirectProductCodeSemantics.productCodeEquiv (leftCode x) (rightCode x)
        (evalWord (DirectProductCode.productCode (leftCode x) (rightCode x)) u) = _
    exact heval

end BenignComapCodeSemantics
end GroupApproximation
