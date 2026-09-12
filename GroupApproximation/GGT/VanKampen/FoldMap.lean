import GroupApproximation.GGT.VanKampen.VertexJoinMap
import GroupApproximation.GGT.VanKampen.CombMapEdgeDeletionConnected
import GroupApproximation.GGT.VanKampen.CombMapEulerUpperBound
import GroupApproximation.Meta.AxiomGuard

set_option linter.unusedSectionVars false

/-!
# Folding a pair of consecutive face darts

Let `p`, `d`, `e` be consecutive darts of one face, so `d` runs from a vertex
`A` to `B` and `e` from `B` to `C`.  When `A ≠ C` the pair `d e` can be folded:

1. join `A` and `C` at the corners after `alpha p` and after `alpha e`
   (`VertexJoin`); the face splits into the digon `d e` and the rest, which
   now runs from `p` directly to the successor of `e` (`joined_facePerm`);
2. delete the edge of `e` (`EdgeDeletion`).  The digon and the face of
   `alpha e` are different faces, so the deletion merges them: `d` takes the
   place of `alpha e`.

The folded map has one vertex and one edge fewer than the original, the same
number of faces, and stays planar.  On labelled discs, with the label of `e`
inverse to that of `d`, this removes the cancelling pair `d e` from the face
word and leaves every other face word unchanged.

The conditions are collected in `IsFoldable`.  The excluded cases are a spur
(`e = alpha d`, handled by spike deletion) and coinciding ends `A = C`.
-/

namespace GroupApproximation.GGT.VanKampen.FoldMap

open Equiv

universe u

variable (M : CombMap.{u}) [DecidableEq M.Dart] (p d e : M.Dart)

/-- The conditions for folding the consecutive darts `d` and `e`, with `p` the
face predecessor of `d`. -/
structure IsFoldable : Prop where
  prev : M.facePerm p = d
  next : M.facePerm d = e
  prev_ne_next : p ≠ e
  not_spur : e ≠ M.alpha d
  distinct_ends : ¬ M.sigma.SameCycle (M.alpha p) (M.alpha e)

/-- The map with the two ends of the pair joined. -/
abbrev joined : CombMap.{u} := VertexJoin.toCombMap M (M.alpha p) (M.alpha e)

instance joinedDecidableEq : DecidableEq (joined M p e).Dart :=
  inferInstanceAs (DecidableEq M.Dart)

/-- The folded map. -/
abbrev toCombMap : CombMap.{u} := EdgeDeletion.toCombMap (joined M p e) e

variable {M p d e}

theorem IsFoldable.ne_next (h : IsFoldable M p d e) : d ≠ e := by
  intro hdeq
  apply h.prev_ne_next
  have h1 : M.facePerm p = M.facePerm d := by rw [h.prev, h.next, hdeq]
  rw [M.facePerm.injective h1, hdeq]

theorem IsFoldable.ne_prev (h : IsFoldable M p d e) : d ≠ p := by
  intro hdp
  apply h.ne_next
  rw [← h.next, hdp, h.prev, hdp]

theorem IsFoldable.ne_alpha_next (h : IsFoldable M p d e) : d ≠ M.alpha e := by
  intro hd
  apply h.not_spur
  rw [hd, M.alpha_involutive]

theorem joined_facePerm : (joined M p e).facePerm = M.facePerm * Equiv.swap p e := by
  show (VertexJoin.toCombMap M (M.alpha p) (M.alpha e)).facePerm = _
  rw [VertexJoin.facePerm_eq, M.alpha_involutive, M.alpha_involutive]

/-- Face rotation of the joined map, at an old dart. -/
theorem joined_facePerm_apply (z : M.Dart) :
    (joined M p e).facePerm z = M.facePerm (Equiv.swap p e z) :=
  congrArg (fun q : Perm (joined M p e).Dart => q z) (joined_facePerm (M := M) (p := p) (e := e))

theorem joined_facePerm_next (h : IsFoldable M p d e) : (joined M p e).facePerm e = d := by
  rw [joined_facePerm_apply, Equiv.swap_apply_right, h.prev]

theorem joined_facePerm_self (h : IsFoldable M p d e) : (joined M p e).facePerm d = e := by
  rw [joined_facePerm_apply, Equiv.swap_apply_of_ne_of_ne h.ne_prev h.ne_next, h.next]

/-- After joining, the rest of the face runs from `p` to the successor of `e`. -/
theorem joined_facePerm_prev : (joined M p e).facePerm p = M.facePerm e := by
  rw [joined_facePerm_apply, Equiv.swap_apply_left]

theorem joined_alpha (x : M.Dart) : (joined M p e).alpha x = M.alpha x := rfl

/-- The pair is consecutive along its face. -/
theorem IsFoldable.sameCycle (h : IsFoldable M p d e) : M.facePerm.SameCycle p e := by
  have hc : M.facePerm.SameCycle p (M.facePerm (M.facePerm p)) :=
    Perm.SameCycle.rfl.apply_right.apply_right
  rwa [h.prev, h.next] at hc

/-- **The joined map is planar.** -/
theorem joined_planar (hM : M.IsPlanar) (h : IsFoldable M p d e) : (joined M p e).IsPlanar := by
  have hne : M.alpha (M.alpha p) ≠ M.alpha (M.alpha e) := by
    rw [M.alpha_involutive, M.alpha_involutive]
    exact h.prev_ne_next
  have hface : M.facePerm.SameCycle (M.alpha (M.alpha p)) (M.alpha (M.alpha e)) := by
    rw [M.alpha_involutive, M.alpha_involutive]
    exact h.sameCycle
  exact VertexJoin.planar M (M.alpha p) (M.alpha e) hM h.distinct_ends hne hface

/-- In the joined map the pair `d e` is a digon, different from the face of
`alpha e`. -/
theorem joined_faceOf_ne (h : IsFoldable M p d e) :
    (joined M p e).faceOf e ≠ (joined M p e).faceOf ((joined M p e).alpha e) := by
  have horbit : ∀ n : ℕ, ((joined M p e).facePerm ^ n) e = e ∨
      ((joined M p e).facePerm ^ n) e = d := by
    intro n
    induction n with
    | zero => exact Or.inl rfl
    | succ n ih =>
        rw [pow_succ', Perm.mul_apply]
        rcases ih with hn | hn
        · rw [hn, joined_facePerm_next h]
          exact Or.inr rfl
        · rw [hn, joined_facePerm_self h]
          exact Or.inl rfl
  intro hface
  obtain ⟨n, hn⟩ := (((joined M p e).faceOf_eq_iff _ _).mp hface).exists_nat_pow_eq
  rcases horbit n with hc | hc
  · rw [hn, joined_alpha] at hc
    exact M.alpha_fixedPointFree e hc
  · rw [hn, joined_alpha] at hc
    exact h.ne_alpha_next hc.symm

/-- The dart `d` survives the deletion of the edge of `e`. -/
def survivor (h : IsFoldable M p d e) : EdgeDeletion.Dart (joined M p e) e :=
  ⟨⟨d, h.ne_next⟩, fun hd => h.ne_alpha_next (congrArg Subtype.val hd)⟩

/-- **The folded map is planar.** -/
theorem planar (hM : M.IsPlanar) (h : IsFoldable M p d e) : (toCombMap M p e).IsPlanar :=
  EdgeDeletion.planar_of_connected (joined M p e) e (joined_planar hM h) (survivor h)
    (EdgeDeletion.connected_of_neFace (joined M p e) e (joined_planar hM h).1
      (joined_faceOf_ne h))

/-- **The fold loses one vertex.** -/
theorem vertexCount_add_one (hM : M.IsPlanar) (h : IsFoldable M p d e) :
    (toCombMap M p e).vertexCount + 1 = M.vertexCount := by
  have hv : (toCombMap M p e).vertexCount = (joined M p e).vertexCount :=
    EdgeDeletion.vertexCount_eq_of_neFace (joined M p e) e (joined_planar hM h).1 (survivor h)
      (joined_faceOf_ne h)
  have hv1 : (joined M p e).vertexCount + 1 = M.vertexCount :=
    VertexJoin.vertexCount_add_one M (M.alpha p) (M.alpha e) h.distinct_ends
  omega

/-- **The fold loses one edge.** -/
theorem edgeCount_add_one : (toCombMap M p e).edgeCount + 1 = M.edgeCount :=
  EdgeDeletion.edgeCount_add_one (joined M p e) e

/-- **The fold keeps the number of faces.** -/
theorem faceCount_eq (hM : M.IsPlanar) (h : IsFoldable M p d e) :
    (toCombMap M p e).faceCount = M.faceCount := by
  have hbal : (toCombMap M p e).faceCount + (joined M p e).vertexCount + 1 =
      (toCombMap M p e).vertexCount + (joined M p e).faceCount :=
    EdgeDeletion.faceCount_balance_of_neFace (joined M p e) e (joined_faceOf_ne h)
  have hv : (toCombMap M p e).vertexCount = (joined M p e).vertexCount :=
    EdgeDeletion.vertexCount_eq_of_neFace (joined M p e) e (joined_planar hM h).1 (survivor h)
      (joined_faceOf_ne h)
  have hne : M.alpha (M.alpha p) ≠ M.alpha (M.alpha e) := by
    rw [M.alpha_involutive, M.alpha_involutive]
    exact h.prev_ne_next
  have hface : M.facePerm.SameCycle (M.alpha (M.alpha p)) (M.alpha (M.alpha e)) := by
    rw [M.alpha_involutive, M.alpha_involutive]
    exact h.sameCycle
  have hf1 : (joined M p e).faceCount = M.faceCount + 1 :=
    VertexJoin.faceCount_eq M (M.alpha p) (M.alpha e) hne hface
  omega

end GroupApproximation.GGT.VanKampen.FoldMap

#audit_axioms GroupApproximation.GGT.VanKampen.FoldMap.joined_facePerm
#audit_axioms GroupApproximation.GGT.VanKampen.FoldMap.joined_facePerm_apply
#audit_axioms GroupApproximation.GGT.VanKampen.FoldMap.joined_planar
#audit_axioms GroupApproximation.GGT.VanKampen.FoldMap.joined_faceOf_ne
#audit_axioms GroupApproximation.GGT.VanKampen.FoldMap.planar
#audit_axioms GroupApproximation.GGT.VanKampen.FoldMap.vertexCount_add_one
#audit_axioms GroupApproximation.GGT.VanKampen.FoldMap.edgeCount_add_one
#audit_axioms GroupApproximation.GGT.VanKampen.FoldMap.faceCount_eq
