import GroupApproximation.GGT.VanKampen.CombMapEdgeSubdivision
import GroupApproximation.GGT.VanKampen.CyclicListExpansion

/-! # Actual face walks after edge subdivision

The chosen dart becomes a two-dart path, and its reverse becomes the
oppositely oriented path. Expanding a face traversal preserves its cyclic
order and introduces no repeated dart.
-/

namespace GroupApproximation.GGT.VanKampen.EdgeSubdivision

open Equiv PermOrbitInsert
universe u
variable (M : CombMap.{u}) (a : M.Dart)

noncomputable local instance : DecidableEq M.Dart := Classical.decEq _

abbrev Dart := EdgeInsertion.Dart M
abbrev embed := EdgeInsertion.embed M

noncomputable def expand (d : M.Dart) : List (Dart M) := by
  classical
  exact if d = a then [none, embed M d]
    else if d = M.alpha a then [embed M d, some none] else [embed M d]

theorem expand_nonempty (d : M.Dart) : expand M a d ≠ [] := by
  classical
  simp only [expand]
  split_ifs <;> simp

theorem expand_head (d : M.Dart) :
    (expand M a d).head (expand_nonempty M a d) = if d = a then none else embed M d := by
  classical
  unfold expand
  split_ifs <;> rfl

theorem expand_last (d : M.Dart) :
    (expand M a d).getLast (expand_nonempty M a d) =
      if d = M.alpha a then some none else embed M d := by
  classical
  by_cases ha : d = a
  · subst d
    simp [expand, (M.alpha_fixedPointFree a).symm]
  · simp only [expand, if_neg ha]
    split_ifs <;> rfl

theorem face_eq_sigma_iff (d : M.Dart) : M.facePerm d = M.sigma a ↔ d = M.alpha a := by
  change M.sigma (M.alpha d) = M.sigma a ↔ d = M.alpha a
  rw [M.sigma.injective.eq_iff]
  constructor
  · intro h
    exact (M.alpha_involutive d).symm.trans (congrArg M.alpha h)
  · intro h
    rw [h, M.alpha_involutive]

theorem step_none : (toCombMap M a).facePerm none = embed M a := by
  change insertBefore (insertBefore M.facePerm (M.sigma a)) (some a) none = some (some a)
  exact insertBefore_none _ _

theorem step_positive : (toCombMap M a).facePerm (some none) =
    if M.sigma a = a then none else embed M (M.sigma a) := by
  classical
  change insertBefore (insertBefore M.facePerm (M.sigma a)) (some a) (some none) = _
  simp only [insertBefore_some, insertBefore_none, Option.some.injEq]
  rfl

theorem step_embed (d : M.Dart) : (toCombMap M a).facePerm (embed M d) =
    if d = M.alpha a then some none else
      if M.facePerm d = a then none else embed M (M.facePerm d) := by
  classical
  refine (congrArg (fun p : Perm (Dart M) => p (embed M d)) (facePerm_eq M a)).trans ?_
  change insertBefore (insertBefore M.facePerm (M.sigma a)) (some a) (some (some d)) = _
  simp only [insertBefore_some, face_eq_sigma_iff]
  split_ifs <;> simp_all [embed, EdgeInsertion.embed]

theorem expand_chain (d : M.Dart) :
    (expand M a d).IsChain (fun x y : Dart M => (toCombMap M a).facePerm x = y) := by
  classical
  by_cases ha : d = a
  · subst d
    simp only [expand, if_true, List.isChain_pair]
    exact step_none M a
  · by_cases hb : d = M.alpha a
    · simp only [expand, if_neg ha, if_pos hb, List.isChain_pair]
      exact (step_embed M a d).trans (if_pos hb)
    · simp [expand, ha, hb]

theorem expand_join (d : M.Dart) :
    (toCombMap M a).facePerm ((expand M a d).getLast (expand_nonempty M a d)) =
      (expand M a (M.facePerm d)).head (expand_nonempty M a _) := by
  classical
  rw [expand_last, expand_head]
  by_cases hd : d = M.alpha a
  · rw [if_pos hd]
    refine (step_positive M a).trans ?_
    rw [hd]
    change (if M.sigma a = a then none else embed M (M.sigma a)) =
      if M.sigma (M.alpha (M.alpha a)) = a then none
        else embed M (M.sigma (M.alpha (M.alpha a)))
    rw [M.alpha_involutive]
  · rw [if_neg hd]
    exact (step_embed M a d).trans (if_neg hd)

def origin : Dart M → M.Dart
  | none => a
  | some none => M.alpha a
  | some (some d) => d

theorem origin_mem_expand (d : M.Dart) (x : Dart M) (hx : x ∈ expand M a d) :
    origin M a x = d := by
  classical
  by_cases ha : d = a
  · subst d
    simp only [expand, if_true, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> rfl
  · by_cases hb : d = M.alpha a
    · simp only [expand, if_neg ha, if_pos hb, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · rfl
      · exact hb.symm
    · simp only [expand, if_neg ha, if_neg hb, List.mem_singleton] at hx
      rw [hx]
      rfl

theorem expand_nodup (d : M.Dart) : (expand M a d).Nodup := by
  classical
  unfold expand
  split_ifs <;> simp [embed, EdgeInsertion.embed]

theorem expanded_nodup (l : List M.Dart) (hl : l.Nodup) : (l.flatMap (expand M a)).Nodup := by
  rw [List.nodup_flatMap]
  refine ⟨fun d _ => expand_nodup M a d, ?_⟩
  apply hl.imp
  intro d e hde
  change List.Disjoint (expand M a d) (expand M a e)
  apply List.disjoint_left.mpr
  intro x hxd hxe
  exact hde ((origin_mem_expand M a d x hxd).symm.trans (origin_mem_expand M a e x hxe))

end GroupApproximation.GGT.VanKampen.EdgeSubdivision

#audit_axioms GroupApproximation.GGT.VanKampen.EdgeSubdivision.expand_chain
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeSubdivision.expand_join
#audit_axioms GroupApproximation.GGT.VanKampen.EdgeSubdivision.expanded_nodup
