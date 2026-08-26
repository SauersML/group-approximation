import GroupApproximation.Computability.DirectProductCode
import GroupApproximation.Computability.PresentationCodeList
import GroupApproximation.Algebra.PresentedGroupRelabel
import GroupApproximation.Algebra.PresentedGroupEvaluation

/-!
# Semantics of the direct-product presentation code

`DirectProductCode.productCode` is a primitive-recursive list constructor.
This file identifies its carrier with the direct product of the two input
carriers, using exactly the two factor relator families and the rectangular
family of cross-generator commutators written by that constructor.
-/

namespace GroupApproximation
namespace DirectProductCodeSemantics

open scoped commutatorElement
open PresentationCodes PresentationCodeList PresentedGroupRelabel
open DirectProductCode RawWord

/-- Consecutive numbering of the two input alphabets in the product code. -/
def productGeneratorEquiv (c d : PresentationCode) :
    Fin (genCount c) ⊕ Fin (genCount d) ≃ Fin (genCount (productCode c d)) :=
  finSumFinEquiv.trans (finCongr (productCode_genCount c d).symm)

@[simp] theorem productGeneratorEquiv_inl (c d : PresentationCode)
    (i : Fin (genCount c)) :
    productGeneratorEquiv c d (Sum.inl i) =
      letterOf (productCode c d) i := by
  apply Fin.ext
  simp only [productGeneratorEquiv, Equiv.trans_apply, finSumFinEquiv_apply_left,
    finCongr_apply, Fin.val_cast, letterOf, productCode_genCount]
  exact (Nat.mod_eq_of_lt
    (lt_of_lt_of_le i.isLt (Nat.le_add_right _ _))).symm

@[simp] theorem productGeneratorEquiv_inr (c d : PresentationCode)
    (j : Fin (genCount d)) :
    productGeneratorEquiv c d (Sum.inr j) =
      letterOf (productCode c d) (genCount c + j) := by
  apply Fin.ext
  simp only [productGeneratorEquiv, Equiv.trans_apply, finSumFinEquiv_apply_right,
    finCongr_apply, Fin.val_cast, letterOf, productCode_genCount]
  exact (Nat.mod_eq_of_lt (Nat.add_lt_add_left j.isLt _)).symm

/-- The product code reads a normalized left word as the left summand word. -/
theorem wordOf_productCode_leftWord (c d : PresentationCode) (w : Raw) :
    wordOf (productCode c d) (leftWord c w) =
      relabel (productGeneratorEquiv c d)
        (FreeGroup.map Sum.inl (wordOf c w)) := by
  show FreeGroup.mk _ = _
  rw [wordOf, FreeGroup.map.mk, relabel, FreeGroup.map.mk]
  congr 1
  simp only [leftWord, List.map_map, Function.comp_def]
  refine List.map_congr_left fun p _ => ?_
  refine Prod.ext ?_ rfl
  rw [productGeneratorEquiv_inl]
  simp only [letterOf]

/-- The product code reads a shifted normalized right word as the right
summand word. -/
theorem wordOf_productCode_rightWord (c d : PresentationCode) (w : Raw) :
    wordOf (productCode c d) (rightWord c d w) =
      relabel (productGeneratorEquiv c d)
        (FreeGroup.map Sum.inr (wordOf d w)) := by
  show FreeGroup.mk _ = _
  rw [wordOf, FreeGroup.map.mk, relabel, FreeGroup.map.mk]
  congr 1
  simp only [rightWord, List.map_map, Function.comp_def]
  refine List.map_congr_left fun p _ => ?_
  refine Prod.ext ?_ rfl
  rw [productGeneratorEquiv_inr]
  simp only [letterOf]

/-- One raw rectangular relator is the corresponding commutator of the two
renumbered free generators. -/
theorem wordOf_productCode_commutatorWord (c d : PresentationCode)
    (i : Fin (genCount c)) (j : Fin (genCount d)) :
    wordOf (productCode c d) (commutatorWord c i j) =
      ⁅FreeGroup.of (productGeneratorEquiv c d (Sum.inl i)),
        FreeGroup.of (productGeneratorEquiv c d (Sum.inr j))⁆ := by
  simp only [commutatorWord, wordOf_cons_pos, wordOf_cons_neg, wordOf_nil,
    mul_one, productGeneratorEquiv_inl, productGeneratorEquiv_inr,
    commutatorElement_def]
  group

end DirectProductCodeSemantics
end GroupApproximation
