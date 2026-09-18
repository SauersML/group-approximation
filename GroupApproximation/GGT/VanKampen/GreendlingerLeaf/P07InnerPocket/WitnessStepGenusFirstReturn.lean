import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepGenusSplit
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Rotate
import GroupApproximation.Meta.AxiomGuard

/-!
# Genus-zero first return of a successor walk

`witnessStepGenus_between_not_mem`: let `N` be planar and let `l` be a duplicate-free
list every cyclic step of which is a successor step (`WitnessStepGenusSucc`: the next
entry is the first kept dart in the vertex run from the reverse, kept meaning in `l` or
reversed into `l`).  If one step `p → q` has `p` and `q` on one face cycle
`p :: (B ++ q :: C)`, then no entry of `l` lies strictly between them, that is, `q` is
the first return of the face walk from `p` to `l`.

Route.  Suppose `p' ∈ B ∩ l`.  The step from `p` runs `m` vertex rotations from `alpha p`;
`m ≥ 2` since otherwise `q` is the face successor of `p`, the head of `B`.  Split the
vertex of `alpha p` at `x = alpha p` and `Y = sigma ^ (m - 1) (alpha p)`.  These lie at one
vertex and their reverses `p`, `alpha Y` lie on the face of `q = facePerm (alpha Y)`, so
the split map has Euler characteristic `4` and `x`, `Y` are separated
(`witnessStepGenus_split_separates`).  But in the split map
* `x` reaches `p` by reversal;
* `p'` reaches `p` along the other steps of `l` (`witnessStepGenus_step_lift`);
* `p'` reaches the head `b` of `B` along the face walk inside `B`
  (`witnessStepGenus_face_lift`), which avoids `p` and `alpha Y`;
* `Y` reaches `b`, since the split rotation sends `Y` to `sigma x = facePerm p = b`.
This connects `x` to `Y`, a contradiction.

This is the genus-zero content of the winding bound: in genus one the statement fails
(`SP/gl-p07-60/first_return.py`: 0 failures in 30098 genus-zero cases, 247 failures in
21617 higher-genus cases).
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness

universe u

/-- **Genus-zero first return.** -/
theorem witnessStepGenus_between_not_mem (N : CombMap.{u}) [DecidableEq N.Dart]
    (hN : N.IsPlanar) {l : List N.Dart} (hl : l.Nodup)
    (hsucc : ∀ (n : ℕ) (s t : List N.Dart) (a b : N.Dart), l.rotate n = s ++ a :: b :: t →
      WitnessStepGenusSucc N l a b)
    {n0 : ℕ} {s0 t0 : List N.Dart} {p q : N.Dart} (hr : l.rotate n0 = s0 ++ p :: q :: t0)
    {B C : List N.Dart} (hΓ : N.IsFaceCycle (p :: (B ++ q :: C))) :
    ∀ e ∈ B, e ∉ l := by
  intro p' hp'B hp'l
  obtain ⟨m, hm0, hmq, hrun⟩ := hsucc n0 s0 t0 p q hr
  have hpl : p ∈ l := (List.mem_rotate (n := n0)).mp (by rw [hr]; simp)
  obtain ⟨b, B', rfl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hp'B)
  obtain ⟨hpnot, hnd'⟩ := List.nodup_cons.mp hΓ.nodup
  have hpB : p ∉ b :: B' := fun h => hpnot (List.mem_append.mpr (Or.inl h))
  have hqB : q ∉ b :: B' := fun h =>
    (List.nodup_append.mp hnd').2.2 q h q (List.mem_cons.mpr (Or.inl rfl)) rfl
  obtain ⟨hhead, htail⟩ := List.isChain_cons.mp hΓ.chain
  have hbφ : N.facePerm p = b := hhead b (by simp)
  have hchainB : List.IsChain (fun d e => N.facePerm d = e) (b :: B') := htail.left_of_append
  have hm2 : 2 ≤ m := by
    by_contra hlt
    have hm1 : m = 1 := by omega
    rw [hm1, pow_one] at hmq
    have hqb : q = b := hmq.symm.trans hbφ
    exact hqB (by rw [hqb]; exact List.mem_cons.mpr (Or.inl rfl))
  have hne : N.alpha p ≠ (N.sigma ^ (m - 1)) (N.alpha p) := by
    intro h
    exact (hrun (m - 1) (by omega) (by omega)).2 (by rw [← h, N.alpha_involutive]; exact hpl)
  have hvert : N.sigma.SameCycle (N.alpha p) ((N.sigma ^ (m - 1)) (N.alpha p)) :=
    Equiv.Perm.sameCycle_pow_right.mpr (Equiv.Perm.SameCycle.refl _ _)
  have hyq : N.facePerm (N.alpha ((N.sigma ^ (m - 1)) (N.alpha p))) = q := by
    rw [← hmq]
    change N.sigma (N.alpha (N.alpha ((N.sigma ^ (m - 1)) (N.alpha p)))) =
      (N.sigma ^ m) (N.alpha p)
    rw [N.alpha_involutive, ← Equiv.Perm.mul_apply N.sigma, ← pow_succ',
      Nat.sub_add_cancel (by omega : 1 ≤ m)]
  have hface : N.facePerm.SameCycle (N.alpha (N.alpha p))
      (N.alpha ((N.sigma ^ (m - 1)) (N.alpha p))) := by
    rw [N.alpha_involutive]
    have hmem := (hΓ.mem_iff q).mp (by simp)
    have hq : N.facePerm.SameCycle p q := ((N.faceOf_eq_iff q p).mp hmem).symm
    rw [← hyq] at hq
    exact Equiv.Perm.sameCycle_apply_right.mp hq
  apply witnessStepGenus_split_separates N hN hvert hne hface
  have hxp : Relation.EqvGen
      (PinchSplit.toCombMap N (N.alpha p) ((N.sigma ^ (m - 1)) (N.alpha p))).Adjacent
      (N.alpha p) p :=
    Relation.EqvGen.rel _ _ (Or.inl (N.alpha_involutive p))
  have hYb : Relation.EqvGen
      (PinchSplit.toCombMap N (N.alpha p) ((N.sigma ^ (m - 1)) (N.alpha p))).Adjacent
      ((N.sigma ^ (m - 1)) (N.alpha p)) b := by
    apply Relation.EqvGen.rel
    right
    change N.sigma (Equiv.swap (N.alpha p) ((N.sigma ^ (m - 1)) (N.alpha p))
      ((N.sigma ^ (m - 1)) (N.alpha p))) = b
    rw [Equiv.swap_apply_right]
    exact hbφ
  have hchainS : List.IsChain (Relation.EqvGen
      (PinchSplit.toCombMap N (N.alpha p) ((N.sigma ^ (m - 1)) (N.alpha p))).Adjacent)
      (b :: B') := by
    refine hchainB.imp_of_mem_imp (fun d e hd he (h : N.facePerm d = e) => ?_)
    rw [← h]
    apply witnessStepGenus_face_lift
    · intro h'
      exact hpB (by rw [← N.alpha.injective h']; exact hd)
    · intro h'
      have heq : e = q := by
        rw [← h, ← hyq, ← h', N.alpha_involutive]
      exact hqB (by rw [← heq]; exact he)
  have hbp' := witnessStepGenus_eqvGen_of_isChain B' b hchainS p' hp'B
  have hrot : l.rotate (n0 + (s0.length + 1)) = q :: (t0 ++ s0) ++ [p] := by
    rw [← List.rotate_rotate, hr]
    have h1 : s0 ++ p :: q :: t0 = (s0 ++ [p]) ++ q :: t0 := by simp
    have hlen : s0.length + 1 = (s0 ++ [p]).length := by simp
    rw [h1, hlen, List.rotate_append_length_eq]
    simp
  have hstepL : ∀ u v e e', q :: (t0 ++ s0) ++ [p] = u ++ e :: e' :: v → e ≠ p →
      Relation.EqvGen
        (PinchSplit.toCombMap N (N.alpha p) ((N.sigma ^ (m - 1)) (N.alpha p))).Adjacent e e' := by
    intro u v e e' h hep
    have hr' : l.rotate (n0 + (s0.length + 1)) = u ++ e :: e' :: v := hrot.trans h
    have hel : e ∈ l := (List.mem_rotate (n := n0 + (s0.length + 1))).mp (by rw [hr']; simp)
    exact witnessStepGenus_step_lift N hm2 hpl hrun hel hep (hsucc _ u v e e' hr')
  have hnd2 : (q :: (t0 ++ s0) ++ [p]).Nodup := by
    rw [← hrot]
    exact List.nodup_rotate.mpr hl
  have hp'p := witnessStepGenus_eqvGen_to_last _ p (q :: (t0 ++ s0)) hnd2 hstepL p'
    (by rw [← hrot]; exact List.mem_rotate.mpr hp'l)
  exact Relation.EqvGen.trans _ _ _ hxp (Relation.EqvGen.trans _ _ _
    (Relation.EqvGen.symm _ _ hp'p) (Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.symm _ _ hbp') (Relation.EqvGen.symm _ _ hYb)))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepGenus_between_not_mem

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness
