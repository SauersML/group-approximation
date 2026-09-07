import GroupApproximation.GGT.VanKampen.CombMapEdgeFaces

/-! # Exact face steps at the two inserted darts -/

namespace GroupApproximation.GGT.VanKampen.EdgeInsertion

open PermOrbitInsert
universe u

theorem facePerm_none_of_ne (M : CombMap.{u}) (a b : M.Dart) (hab : a ≠ b) :
    (toCombMap M a b).facePerm none = embed M a := by
  classical
  change insertBefore (insertBefore M.sigma a) (some b) (some none) = some (some a)
  simp only [insertBefore_some, insertBefore_none, Option.some.injEq, if_neg hab]

theorem facePerm_none_of_eq (M : CombMap.{u}) (a : M.Dart) :
    (toCombMap M a a).facePerm none = none := by
  classical
  change insertBefore (insertBefore M.sigma a) (some a) (some none) = none
  simp [insertBefore_some]

theorem facePerm_positive (M : CombMap.{u}) (a b : M.Dart) :
    (toCombMap M a b).facePerm (some none) = embed M b := by
  change insertBefore (insertBefore M.sigma a) (some b) none = some (some b)
  exact insertBefore_none _ _

theorem facePerm_embed_left (M : CombMap.{u}) (a b d : M.Dart)
    (ha : M.facePerm d = a) :
    (toCombMap M a b).facePerm (embed M d) = some none := by
  classical
  change insertBefore (insertBefore M.sigma a) (some b) (some (some (M.alpha d))) = some none
  change M.sigma (M.alpha d) = a at ha
  simp only [insertBefore_some, if_pos ha, reduceCtorEq, if_false]

theorem facePerm_embed_right (M : CombMap.{u}) (a b d : M.Dart)
    (ha : M.facePerm d ≠ a) (hb : M.facePerm d = b) :
    (toCombMap M a b).facePerm (embed M d) = none := by
  classical
  change insertBefore (insertBefore M.sigma a) (some b) (some (some (M.alpha d))) = none
  change M.sigma (M.alpha d) ≠ a at ha
  change M.sigma (M.alpha d) = b at hb
  simp only [insertBefore_some, if_neg ha, Option.some.injEq, if_pos hb]

theorem facePerm_embed_other (M : CombMap.{u}) (a b d : M.Dart)
    (ha : M.facePerm d ≠ a) (hb : M.facePerm d ≠ b) :
    (toCombMap M a b).facePerm (embed M d) = embed M (M.facePerm d) := by
  classical
  change insertBefore (insertBefore M.sigma a) (some b) (some (some (M.alpha d))) =
    some (some (M.sigma (M.alpha d)))
  change M.sigma (M.alpha d) ≠ a at ha
  change M.sigma (M.alpha d) ≠ b at hb
  simp only [insertBefore_some, if_neg ha, Option.some.injEq, if_neg hb]

end GroupApproximation.GGT.VanKampen.EdgeInsertion

#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.facePerm_embed_left
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.facePerm_embed_right
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeInsertion.facePerm_embed_other
