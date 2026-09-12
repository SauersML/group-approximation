import GroupApproximation.GGT.VanKampen.DartExpansion

/-! # Edge subdivision as an actual reversible dart expansion -/

namespace GroupApproximation.GGT.VanKampen.EdgeSubdivision

universe u
variable (M : CombMap.{u}) (a : M.Dart)

theorem expand_alpha (d : M.Dart) :
    expand M a (M.alpha d) = (expand M a d).reverse.map (toCombMap M a).alpha := by
  classical
  have hm (l : List (Dart M)) : l.map (toCombMap M a).alpha = l.map (EdgeInsertion.alphaFun M) := by
    apply List.map_congr_left
    intro x _
    rcases x with _ | (_ | x) <;> rfl
  refine Eq.trans (b := (expand M a d).reverse.map (EdgeInsertion.alphaFun M)) ?_ (hm _).symm
  by_cases ha : d = a
  · subst d
    simp [expand, M.alpha_fixedPointFree a, embed, EdgeInsertion.embed, EdgeInsertion.alphaFun]
  · by_cases hb : d = M.alpha a
    · subst d
      simp [expand, M.alpha_fixedPointFree a, M.alpha_involutive a, embed,
        EdgeInsertion.embed, EdgeInsertion.alphaFun]
    · have hda : M.alpha d ≠ a := by
        intro h
        exact hb ((M.alpha_involutive d).symm.trans (congrArg M.alpha h))
      have hdb : M.alpha d ≠ M.alpha a := fun h => ha (M.alpha.injective h)
      simp [expand, ha, hb, hda, hdb, embed, EdgeInsertion.embed, EdgeInsertion.alphaFun]

noncomputable def dartExpansion : DartExpansion M (toCombMap M a) where
  darts := expand M a
  nonempty := expand_nonempty M a
  nodup := expanded_nodup M a
  chain := expand_chain M a
  join := expand_join M a
  reverse := expand_alpha M a

end GroupApproximation.GGT.VanKampen.EdgeSubdivision

#audit_axioms GroupApproximation.GGT.VanKampen.EdgeSubdivision.dartExpansion
