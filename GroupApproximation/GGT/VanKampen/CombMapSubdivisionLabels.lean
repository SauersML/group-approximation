import GroupApproximation.GGT.VanKampen.CombMapSubdivisionBoundary
import GroupApproximation.GGT.HullSCRelatorAdmissible

/-! # Labels and face words for actual edge subdivision

Replace the chosen label by two letters with the same product. The reverse
path receives their formal inverses in reverse order. All expanded face
words retain their based values; words avoiding the edge are unchanged.
-/

namespace GroupApproximation.GGT.VanKampen.EdgeSubdivision

open HullSC HullSC.Lemma44OrientedRelatorDiagram
universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
variable (M : CombMap.{v}) (a : M.Dart)
variable (oldLabel : M.Dart → RelLetter G Lambda) (left right : RelLetter G Lambda)

noncomputable def subdivideLabel : Dart M → RelLetter G Lambda := by
  classical
  exact fun x => match x with
    | none => left
    | some none => RelWord.inv left
    | some (some d) =>
        if d = a then right else if d = M.alpha a then RelWord.inv right else oldLabel d

theorem subdivideLabel_alpha
    (hlabel : ∀ d, oldLabel (M.alpha d) = RelWord.inv (oldLabel d)) (d : Dart M) :
    subdivideLabel M a oldLabel left right ((toCombMap M a).alpha d) =
      RelWord.inv (subdivideLabel M a oldLabel left right d) := by
  classical
  rcases d with _ | (_ | d)
  · rfl
  · exact (RelWord.inv_inv_letter left).symm
  · change subdivideLabel M a oldLabel left right (embed M (M.alpha d)) =
      RelWord.inv (subdivideLabel M a oldLabel left right (embed M d))
    by_cases ha : d = a
    · subst d
      simp [subdivideLabel, embed, EdgeInsertion.embed, M.alpha_fixedPointFree a]
    · by_cases hb : d = M.alpha a
      · subst d
        simp [subdivideLabel, embed, EdgeInsertion.embed, M.alpha_fixedPointFree a,
          M.alpha_involutive a, RelWord.inv_inv_letter]
      · have hda : M.alpha d ≠ a := by
          intro h
          exact hb ((M.alpha_involutive d).symm.trans (congrArg M.alpha h))
        have hdb : M.alpha d ≠ M.alpha a := fun h => ha (M.alpha.injective h)
        simp only [subdivideLabel, embed, EdgeInsertion.embed, if_neg ha, if_neg hb,
          if_neg hda, if_neg hdb]
        exact hlabel d

theorem expanded_letter_value
    (hlabel : ∀ d, oldLabel (M.alpha d) = RelWord.inv (oldLabel d))
    (hfactor : (oldLabel a).val = left.val * right.val) (d : M.Dart) :
    RelLetter.listVal ((expand M a d).map (subdivideLabel M a oldLabel left right)) =
      (oldLabel d).val := by
  classical
  by_cases ha : d = a
  · subst d
    simpa [expand, subdivideLabel, embed, EdgeInsertion.embed, RelWord.listVal_cons,
      RelLetter.listVal] using hfactor.symm
  · by_cases hb : d = M.alpha a
    · subst d
      simp [expand, subdivideLabel, embed, EdgeInsertion.embed, M.alpha_fixedPointFree a,
        RelLetter.listVal, RelWord.val_inv, hlabel a, hfactor, mul_inv_rev]
    · simp [expand, subdivideLabel, embed, EdgeInsertion.embed, ha, hb,
        RelLetter.listVal]

theorem expanded_word_value
    (hlabel : ∀ d, oldLabel (M.alpha d) = RelWord.inv (oldLabel d))
    (hfactor : (oldLabel a).val = left.val * right.val) (l : List M.Dart) :
    RelLetter.listVal ((l.flatMap (expand M a)).map (subdivideLabel M a oldLabel left right)) =
      RelLetter.listVal (l.map oldLabel) := by
  induction l with
  | nil => rfl
  | cons d l ih =>
      rw [List.flatMap_cons, List.map_append, RelWord.listVal_append,
        expanded_letter_value M a oldLabel left right hlabel hfactor, ih,
        List.map_cons, RelWord.listVal_cons]

theorem expanded_word_kept (l : List M.Dart) (ha : a ∉ l) (hb : M.alpha a ∉ l) :
    (l.flatMap (expand M a)).map (subdivideLabel M a oldLabel left right) = l.map oldLabel := by
  classical
  induction l with
  | nil => rfl
  | cons d l ih =>
      have hda : d ≠ a := fun h => ha (by simp [h])
      have hdb : d ≠ M.alpha a := fun h => hb (by simp [h])
      have hla : a ∉ l := fun h => ha (List.mem_cons_of_mem d h)
      have hlb : M.alpha a ∉ l := fun h => hb (List.mem_cons_of_mem d h)
      simp only [List.flatMap_cons, expand, if_neg hda, if_neg hdb, List.singleton_append,
        List.map_cons, subdivideLabel, embed, EdgeInsertion.embed, ih hla hlb]

theorem subdivideLabel_admissible_of_inv (D : RelGenSet G Lambda)
    (hlabel : ∀ d, d ≠ a → d ≠ M.alpha a → D.IsLetter (oldLabel d))
    (hleft : D.IsLetter left) (hleftInv : D.IsLetter (RelWord.inv left))
    (hright : D.IsLetter right) (hrightInv : D.IsLetter (RelWord.inv right)) (d : Dart M) :
    D.IsLetter (subdivideLabel M a oldLabel left right d) := by
  classical
  rcases d with _ | (_ | d)
  · exact hleft
  · exact hleftInv
  · change D.IsLetter (if d = a then right else if d = M.alpha a then RelWord.inv right else oldLabel d)
    split_ifs with ha hb
    · exact hright
    · exact hrightInv
    · exact hlabel d ha hb

theorem subdivideLabel_admissible (D : RelGenSet G Lambda)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (hlabel : ∀ d, d ≠ a → d ≠ M.alpha a → D.IsLetter (oldLabel d))
    (hleft : D.IsLetter left) (hright : D.IsLetter right) (d : Dart M) :
    D.IsLetter (subdivideLabel M a oldLabel left right d) :=
  subdivideLabel_admissible_of_inv M a oldLabel left right D hlabel
    hleft (isLetter_relWordInv D hsymm hleft)
    hright (isLetter_relWordInv D hsymm hright) d

theorem allBoundary_value (FB : ∀ f : M.Face, FaceBoundary M f)
    (hlabel : ∀ d, oldLabel (M.alpha d) = RelWord.inv (oldLabel d))
    (hfactor : (oldLabel a).val = left.val * right.val) (f : M.Face) :
    RelLetter.listVal ((allBoundary M a FB ((faceEquiv M a).symm f)).darts.map
      (subdivideLabel M a oldLabel left right)) = RelLetter.listVal ((FB f).darts.map oldLabel) := by
  rw [allBoundary_darts M a FB f]
  exact expanded_word_value M a oldLabel left right hlabel hfactor _

theorem allBoundary_word_kept (FB : ∀ f : M.Face, FaceBoundary M f)
    (f : M.Face) (ha : M.faceOf a ≠ f) (hb : M.faceOf (M.alpha a) ≠ f) :
    (allBoundary M a FB ((faceEquiv M a).symm f)).darts.map
      (subdivideLabel M a oldLabel left right) = (FB f).darts.map oldLabel := by
  rw [allBoundary_darts M a FB f]
  apply expanded_word_kept M a oldLabel left right
  · exact fun h => ha (((FB f).mem_iff a).mp h)
  · exact fun h => hb (((FB f).mem_iff (M.alpha a)).mp h)

end GroupApproximation.GGT.VanKampen.EdgeSubdivision

#audit_axioms GroupApproximation.GGT.VanKampen.EdgeSubdivision.subdivideLabel_alpha
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeSubdivision.expanded_word_value
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeSubdivision.allBoundary_word_kept
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeSubdivision.subdivideLabel_admissible
