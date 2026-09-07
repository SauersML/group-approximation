import GroupApproximation.GGT.VanKampen.CombMapEdgeBoundaries
import GroupApproximation.GGT.HullSCRelatorAdmissible

/-!
# Labels on a split G-face

The inserted positive dart receives the chosen relative letter, and the
negative dart its formal inverse. If that letter represents the old prefix,
both newly constructed face boundaries have value one in the ambient group.
-/

namespace GroupApproximation.GGT.VanKampen.EdgeInsertion

open HullSC HullSC.Lemma44OrientedRelatorDiagram
universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
variable (M : CombMap.{v})

def insertLabel (oldLabel : M.Dart → RelLetter G Lambda) (letter : RelLetter G Lambda) :
    Dart M → RelLetter G Lambda
  | none => RelWord.inv letter
  | some none => letter
  | some (some d) => oldLabel d

theorem insertLabel_alpha (oldLabel : M.Dart → RelLetter G Lambda)
    (hlabel : ∀ d, oldLabel (M.alpha d) = RelWord.inv (oldLabel d))
    (letter : RelLetter G Lambda) (a b : M.Dart) (d : Dart M) :
    insertLabel M oldLabel letter ((toCombMap M a b).alpha d) =
      RelWord.inv (insertLabel M oldLabel letter d) := by
  rcases d with _ | (_ | d)
  · exact (RelWord.inv_inv_letter letter).symm
  · rfl
  · exact hlabel d

theorem insertLabel_admissible (D : RelGenSet G Lambda)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (oldLabel : M.Dart → RelLetter G Lambda) (hlabel : ∀ d, D.IsLetter (oldLabel d))
    (letter : RelLetter G Lambda) (hletter : D.IsLetter letter) (d : Dart M) :
    D.IsLetter (insertLabel M oldLabel letter d) := by
  rcases d with _ | (_ | d)
  · exact isLetter_relWordInv D hsymm hletter
  · exact hletter
  · exact hlabel d

variable {f : M.Face} (B : FaceBoundary M f) (FB : ∀ g : M.Face, FaceBoundary M g)

theorem split_prefix_word (k : Fin B.darts.length)
    (oldLabel : M.Dart → RelLetter G Lambda) (letter : RelLetter G Lambda) :
    (allFaceBoundary M B FB k (prefixFace M B k)).darts.map (insertLabel M oldLabel letter) =
      RelWord.inv letter :: (B.darts.take k.val).map oldLabel := by
  rw [allFaceBoundary_prefix]
  simp only [prefixDarts, List.map_cons, List.map_map]
  rfl

theorem split_suffix_word (k : Fin B.darts.length)
    (oldLabel : M.Dart → RelLetter G Lambda) (letter : RelLetter G Lambda) :
    (allFaceBoundary M B FB k (suffixFace M B k)).darts.map (insertLabel M oldLabel letter) =
      letter :: (B.darts.drop k.val).map oldLabel := by
  rw [allFaceBoundary_suffix]
  simp only [suffixDarts, List.map_cons, List.map_map]
  rfl

theorem split_kept_word (k : Fin B.darts.length) (g : M.Face) (hg : g ≠ f)
    (oldLabel : M.Dart → RelLetter G Lambda) (letter : RelLetter G Lambda) :
    (allFaceBoundary M B FB k (keptFace M (firstCorner M B) (secondCorner M B k) g)).darts.map
      (insertLabel M oldLabel letter) = (FB g).darts.map oldLabel := by
  rw [allFaceBoundary_kept M B FB k g hg, List.map_map]
  rfl

theorem split_prefix_null (k : Fin B.darts.length)
    (oldLabel : M.Dart → RelLetter G Lambda) (letter : RelLetter G Lambda)
    (hprefix : letter.val = RelLetter.listVal ((B.darts.take k.val).map oldLabel)) :
    RelLetter.listVal ((allFaceBoundary M B FB k (prefixFace M B k)).darts.map
      (insertLabel M oldLabel letter)) = 1 := by
  rw [split_prefix_word, RelWord.listVal_cons, RelWord.val_inv, hprefix, inv_mul_cancel]

theorem split_suffix_null (k : Fin B.darts.length)
    (oldLabel : M.Dart → RelLetter G Lambda) (letter : RelLetter G Lambda)
    (hprefix : letter.val = RelLetter.listVal ((B.darts.take k.val).map oldLabel))
    (hwhole : RelLetter.listVal (B.darts.map oldLabel) = 1) :
    RelLetter.listVal ((allFaceBoundary M B FB k (suffixFace M B k)).darts.map
      (insertLabel M oldLabel letter)) = 1 := by
  rw [split_suffix_word, RelWord.listVal_cons, hprefix, ← RelWord.listVal_append,
    ← List.map_append, List.take_append_drop]
  exact hwhole

end GroupApproximation.GGT.VanKampen.EdgeInsertion

#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.insertLabel_alpha
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.insertLabel_admissible
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.split_kept_word
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.split_prefix_null
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.split_suffix_null
