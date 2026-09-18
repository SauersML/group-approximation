import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepSubRestrict
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepGenusProof
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepBridgeLift
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessCurveSublistRotate
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-65: nested successor walks in a planar map

Lane gl-p07-65.  Certifies no printed sentence on its own.  NOT COMPILED.

Let `M` be planar and let `L` and `l ⊆ L` be duplicate-free walks, each of whose cyclic steps is
a successor step (`WitnessStepGenusSucc`) relative to itself.  Then some rotation of `l` is a
sublist of `L` (`witnessStepSub_nested_sublist`).

Route (genus zero; planarity is used essentially).  Restrict `M` to the edges of `L`
(`walkMap M L`).  The lift `Γ` of `L` is a face cycle of the restriction, the restriction is
connected and so planar (`WitnessStepSubRestrict`).  The lift of `l` has successor steps in the
restriction (`witnessStepSub_succ_lift`).  The genus-zero split and first-return argument
`witnessStepGenus_stepNext_of_model` then gives each step of `l` as a forward step of `L`, and
`exists_rotate_sublist_of_steps` assembles the sublist.  In higher genus the first-return lemma
fails, and so does this statement.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u

open SimpleClosedWalkSides

namespace FourPieceWitness

/-- **Each step of a nested successor walk is a forward step of the outer one.** -/
theorem witnessStepSub_nested_steps (M : CombMap.{u}) (hM : M.IsPlanar) {L l : List M.Dart}
    (hL : L.Nodup) (hl : l.Nodup) (hsub : ∀ e ∈ l, e ∈ L)
    (hLs : ∀ (n : ℕ) (s t : List M.Dart) (x y : M.Dart), L.rotate n = s ++ x :: y :: t →
      WitnessStepGenusSucc M L x y)
    (hls : ∀ (n : ℕ) (s t : List M.Dart) (x y : M.Dart), l.rotate n = s ++ x :: y :: t →
      WitnessStepGenusSucc M l x y) :
    ∀ (n : ℕ) (s t : List M.Dart) (x y : M.Dart), l.rotate n = s ++ x :: y :: t →
      WitnessCurveSublistList.StepNext L l x y := by
  classical
  intro n s t x y hr
  have hxy : x ≠ y := witnessStepGenus_ne_of_rotate hl hr
  have hxl : x ∈ l := (List.mem_rotate (n := n)).mp (by rw [hr]; simp)
  have hyl : y ∈ l := (List.mem_rotate (n := n)).mp (by rw [hr]; simp)
  have hkL := witnessStepSub_keepSelf M L
  have hkl : ∀ e ∈ l, walkKeep M L e := fun e he => Or.inl (hsub e he)
  have hΓmap := witnessStepSub_lift_map M L L hkL
  have hl'map := witnessStepSub_lift_map M L l hkl
  -- the lift of `L` is a face cycle of the restriction
  have hΓsteps : ∀ (n : ℕ) (s t : List (walkMap M L).Dart) (c d : (walkMap M L).Dart),
      (witnessStepSub_lift M L L hkL).rotate n = s ++ c :: d :: t →
      (walkMap M L).facePerm c = d := by
    intro n s t c d h
    exact witnessStepSub_facePerm_of_succ _ _ (witnessStepSub_cover M L)
      (witnessStepSub_succ_lift M L L hkL c d (hLs n _ _ _ _
        (witnessStepBridge_rotate_val hΓmap h)))
  have hlen : 2 ≤ (witnessStepSub_lift M L L hkL).length := by
    rw [witnessStepSub_lift_length]
    exact witnessStepSub_two_le_length (hsub x hxl) (hsub y hyl) hxy
  have hΓ : (walkMap M L).IsFaceCycle (witnessStepSub_lift M L L hkL) :=
    witnessStepSub_isFaceCycle_of_steps _ hlen (witnessStepSub_lift_nodup M L L hkL hL)
      hΓsteps
  have hconn : (walkMap M L).IsConnected :=
    witnessStepSub_connected _ hΓ (witnessStepSub_cover M L)
  have hN : (walkMap M L).IsPlanar :=
    (walkMap_isRestriction M L).planar hM hconn
      ((witnessStepSub_lift M L L hkL).head hΓ.ne_nil)
  -- the lift of `l` has successor steps in the restriction
  have hsucc : ∀ (n : ℕ) (s t : List (walkMap M L).Dart) (c d : (walkMap M L).Dart),
      (witnessStepSub_lift M L l hkl).rotate n = s ++ c :: d :: t →
      WitnessStepGenusSucc (walkMap M L) (witnessStepSub_lift M L l hkl) c d := by
    intro n s t c d h
    exact witnessStepSub_succ_lift M L l hkl c d
      (hls n _ _ _ _ (witnessStepBridge_rotate_val hl'map h))
  have hsub' : ∀ d ∈ witnessStepSub_lift M L l hkl, d ∈ witnessStepSub_lift M L L hkL :=
    fun d hd => (witnessStepSub_mem_lift M L L hkL d).mpr
      (hsub _ ((witnessStepSub_mem_lift M L l hkl d).mp hd))
  have hcompat : ∀ c ∈ witnessStepSub_lift M L l hkl, ∀ d ∈ witnessStepSub_lift M L l hkl,
      (WitnessStepGenusBefore L (Subtype.val c) (Subtype.val d) ↔
        WitnessStepGenusBefore (witnessStepSub_lift M L L hkL) c d) := by
    intro c _ d _
    have key : ∀ L₀ : List M.Dart, (witnessStepSub_lift M L L hkL).map Subtype.val = L₀ →
        (WitnessStepGenusBefore L₀ (Subtype.val c) (Subtype.val d) ↔
          WitnessStepGenusBefore (witnessStepSub_lift M L L hkL) c d) := by
      rintro L₀ rfl
      exact witnessStepBridge_before_map Subtype.val_injective
    exact key L hΓmap
  have hmem : ∀ d ∈ witnessStepSub_lift M L l hkl, Subtype.val d ∈ L :=
    fun d hd => hsub _ ((witnessStepSub_mem_lift M L l hkl d).mp hd)
  have hstep := witnessStepGenus_stepNext_of_model (walkMap M L) hN Subtype.val L
    (witnessStepSub_lift_nodup M L l hkl hl) hsucc hΓ hsub' hcompat hmem
  have key : ∀ l₀ : List M.Dart, (witnessStepSub_lift M L l hkl).map Subtype.val = l₀ →
      l₀.rotate n = s ++ x :: y :: t → WitnessCurveSublistList.StepNext L l₀ x y := by
    rintro l₀ rfl h
    exact hstep n s t x y h
  exact key l hl'map hr

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepSub_nested_steps

/-- **Nested successor walks in a planar map: a rotation of the inner walk is a sublist of the
outer walk.** -/
theorem witnessStepSub_nested_sublist (M : CombMap.{u}) (hM : M.IsPlanar) {L l : List M.Dart}
    (hL : L.Nodup) (hl : l.Nodup) (hsub : ∀ e ∈ l, e ∈ L)
    (hLs : ∀ (n : ℕ) (s t : List M.Dart) (x y : M.Dart), L.rotate n = s ++ x :: y :: t →
      WitnessStepGenusSucc M L x y)
    (hls : ∀ (n : ℕ) (s t : List M.Dart) (x y : M.Dart), l.rotate n = s ++ x :: y :: t →
      WitnessStepGenusSucc M l x y) :
    ∃ n : ℕ, l.rotate n <+ L :=
  WitnessCurveSublistList.exists_rotate_sublist_of_steps hL hl hsub
    (witnessStepSub_nested_steps M hM hL hl hsub hLs hls)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepSub_nested_sublist

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
