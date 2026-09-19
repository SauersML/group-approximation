import GroupApproximation.Computability.BenignInfCode
import GroupApproximation.Computability.DirectProductCodeSemantics

/-!
# Semantics of the effective benign-intersection syntax

The syntax transform in `BenignInfCode` forms a direct-product presentation,
puts the two cutter lists in the two factors, and puts each pair of marked
words on the diagonal.  This file records those three facts at the actual
`PresentationCode` carriers.  They are the word-level input needed to identify
the computed syntax with `Higman.BenignWitness.inf`.
-/

namespace GroupApproximation
namespace BenignInfCodeSemantics

open PresentationCodes DirectProductCodeSemantics
open BenignInfCode

/-- Evaluation of a raw word in the group carried by a presentation code. -/
def evalWord (c : PresentationCode) (w : Raw) : Carrier c :=
  PresentedGroup.mk (codeRels c) (wordOf c w)

/-- A transformed left word evaluates in the left direct-product factor. -/
theorem productCodeEquiv_eval_leftWord (c d : PresentationCode) (w : Raw) :
    productCodeEquiv c d (evalWord (DirectProductCode.productCode c d)
      (DirectProductCode.leftWord c w)) =
      ((evalWord c w, 1) : Carrier c × Carrier d) := by
  exact productCodeEquiv_leftWord c d w

/-- A transformed right word evaluates in the right direct-product factor. -/
theorem productCodeEquiv_eval_rightWord (c d : PresentationCode) (w : Raw) :
    productCodeEquiv c d (evalWord (DirectProductCode.productCode c d)
      (DirectProductCode.rightWord c d w)) =
      ((1, evalWord d w) : Carrier c × Carrier d) := by
  exact productCodeEquiv_rightWord c d w

/-- Raw-word evaluation respects concatenation. -/
theorem evalWord_append (c : PresentationCode) (u v : Raw) :
    evalWord c (u ++ v) = evalWord c u * evalWord c v := by
  unfold evalWord
  rw [RawWord.wordOf_append, map_mul]

/-- The `i`-th computed diagonal mark is the pair of the two input marks. -/
theorem productCodeEquiv_diagonalAt (x : Input) (i : ℕ) :
    productCodeEquiv (leftCode x) (rightCode x)
        (evalWord (transform x).1 (diagonalAt x i)) =
      (evalWord (leftCode x) ((leftMarks x).getD i []),
        evalWord (rightCode x) ((rightMarks x).getD i [])) := by
  change productCodeEquiv (leftCode x) (rightCode x)
      (evalWord (DirectProductCode.productCode (leftCode x) (rightCode x))
        (diagonalAt x i)) = _
  rw [diagonalAt, evalWord_append, map_mul,
    productCodeEquiv_eval_leftWord, productCodeEquiv_eval_rightWord]
  simp

/-- Every word in the computed left cutter lands in the old left cutter and
the identity of the right factor. -/
theorem exists_leftCuttingWord (x : Input) {w : Raw}
    (hw : w ∈ leftCutter x) :
    ∃ u ∈ leftCuttingWords x,
      productCodeEquiv (leftCode x) (rightCode x)
          (evalWord (DirectProductCode.productCode (leftCode x) (rightCode x)) u) =
        ((evalWord (leftCode x) w, 1) : Carrier (leftCode x) ×
          Carrier (rightCode x)) := by
  refine ⟨DirectProductCode.leftWord (leftCode x) w, ?_, ?_⟩
  · exact List.mem_map.mpr ⟨w, hw, rfl⟩
  · exact productCodeEquiv_eval_leftWord _ _ _

/-- Every word in the computed right cutter lands in the old right cutter and
the identity of the left factor. -/
theorem exists_rightCuttingWord (x : Input) {w : Raw}
    (hw : w ∈ rightCutter x) :
    ∃ u ∈ rightCuttingWords x,
      productCodeEquiv (leftCode x) (rightCode x)
          (evalWord (DirectProductCode.productCode (leftCode x) (rightCode x)) u) =
        ((1, evalWord (rightCode x) w) : Carrier (leftCode x) ×
          Carrier (rightCode x)) := by
  refine ⟨DirectProductCode.rightWord (leftCode x) (rightCode x) w, ?_, ?_⟩
  · exact List.mem_map.mpr ⟨w, hw, rfl⟩
  · exact productCodeEquiv_eval_rightWord _ _ _

end BenignInfCodeSemantics
end GroupApproximation
