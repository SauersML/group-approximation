import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRunSplit
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-26: rotated blocks of an enclosed walk are face chains

Let `E : EnclosedFaceSetSucc X F ow` and `ow.rotate s = u ++ v`.  Write `p(t) = (t + s) % |ow|`,
so that `(ow.rotate s)[t] = ow[p(t)]`.

## Proof route

1. `ArcClose.mem_of_rotate` and `ArcClose.mem_of_rotate_succ`: for `t < |u|`, `ow[p(t)]` is the
   block entry `u[t]`.  For `t + 1 < |u|`, `ow[(p(t) + 1) % |ow|]` is `u[t+1]`, by
   `Nat.mod_add_mod`.
2. `ArcClose.step_of_keep_or_pinch`: if `facePerm ow[p]` is kept, or `ow[p]` is pinch-free and the
   next dart lies on the same face, then `facePerm ow[p]` is the next walk dart.  This uses
   `PocketRun.succ_eq_facePerm_of_keep` and `_of_pinchFree` (lane gl-p07-09).
3. `ArcClose.rotate_step`: a step at `p(t)` is a step of the rotated list at `t`
   (`List.getElem_rotate`).
4. `ArcClose.rotate_chain_step`: the block `u` lies on a cell arc `A` and every `p(t)` with
   `t + 1 < |u|` is kept or pinch-free.  Then `u` is a `facePerm` chain.  Both darts lie on the
   cell face (`PocketRun.arcFaceOf`), so the pinch case applies.
5. `ArcClose.exists_cellArc_of_rotate`: such a block is a sub-arc
   (`PocketRun.exists_cellArc_of_isChain`).
6. `ArcClose.add_succ_mod_ne`: `(t + (p + 1)) % n ≠ p` for `t + 1 < n` and `p < n`.  This is the
   index bookkeeping for the rotation after the unique junction.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded SimpleClosedWalkSides

namespace ArcClose

/-- **The index after the junction is not the junction.** -/
theorem add_succ_mod_ne {t p n : ℕ} (ht : t + 1 < n) (hp : p < n) : (t + (p + 1)) % n ≠ p := by
  intro h
  by_cases hlt : t + (p + 1) < n
  · rw [Nat.mod_eq_of_lt hlt] at h
    omega
  · rw [Nat.mod_eq_sub_mod (show t + (p + 1) ≥ n by omega),
      Nat.mod_eq_of_lt (show t + (p + 1) - n < n by omega)] at h
    omega

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.ArcClose.add_succ_mod_ne

/-- An index of a block is an index of the rotated list. -/
theorem lt_length_rotate {α : Type*} {ow u v : List α} {s t : ℕ} (hs : ow.rotate s = u ++ v)
    (ht : t < u.length) : t < (ow.rotate s).length := by
  rw [hs, List.length_append]
  omega

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.ArcClose.lt_length_rotate

/-- **A rotated position of a block entry lies in the block.** -/
theorem mem_of_rotate {α : Type*} {ow u v : List α} {s : ℕ} (hs : ow.rotate s = u ++ v)
    (t : ℕ) (ht : t < u.length) (hp : (t + s) % ow.length < ow.length) :
    ow[(t + s) % ow.length]'hp ∈ u := by
  have h0 := lt_length_rotate hs ht
  have e : ow[(t + s) % ow.length]'hp = u[t] :=
    (List.getElem_rotate ow s t h0).symm.trans
      ((List.getElem_of_eq hs h0).trans (List.getElem_append_left ht))
  rw [e]
  exact List.getElem_mem ht

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.ArcClose.mem_of_rotate

/-- **The successor of a rotated position of a block entry lies in the block.** -/
theorem mem_of_rotate_succ {α : Type*} {ow u v : List α} {s : ℕ} (hs : ow.rotate s = u ++ v)
    (t : ℕ) (ht : t + 1 < u.length) (hp : (t + s) % ow.length < ow.length) :
    ow[((t + s) % ow.length + 1) % ow.length]'(Nat.mod_lt _
      (Nat.lt_of_le_of_lt (Nat.zero_le _) hp)) ∈ u := by
  have h0 := lt_length_rotate hs ht
  have e : ow[((t + s) % ow.length + 1) % ow.length]'(Nat.mod_lt _
      (Nat.lt_of_le_of_lt (Nat.zero_le _) hp)) = u[t + 1] :=
    (PocketRun.getElem_idx_congr ow (by rw [Nat.mod_add_mod, Nat.add_right_comm t s 1]) _ _).trans
      ((List.getElem_rotate ow s (t + 1) h0).symm.trans
        ((List.getElem_of_eq hs h0).trans (List.getElem_append_left ht)))
  rw [e]
  exact List.getElem_mem ht

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.ArcClose.mem_of_rotate_succ

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {X : DiscDiagram.{u, w, v} W} {F : Finset X.toCombMap.Face} {ow : List X.toCombMap.Dart}

/-- **A kept or pinch-free position is a face step.** -/
theorem step_of_keep_or_pinch (E : EnclosedFaceSetSucc X F ow) (p : ℕ) (hp : p < ow.length)
    (h : walkKeep X.toCombMap ow (X.toCombMap.facePerm ow[p]) ∨
      PocketRun.PinchFreeAt X.toCombMap ow[p])
    (hface : X.toCombMap.faceOf
        (ow[(p + 1) % ow.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le p) hp))) =
      X.toCombMap.faceOf ow[p]) :
    X.toCombMap.facePerm ow[p] =
      ow[(p + 1) % ow.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le p) hp)) := by
  rcases h with hkeep | hpinch
  · exact PocketRun.succ_eq_facePerm_of_keep E p hp hkeep
  · exact PocketRun.succ_eq_facePerm_of_pinchFree E p hp hpinch hface

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.ArcClose.step_of_keep_or_pinch

/-- **A step at a rotated position is a step of the rotated list.** -/
theorem rotate_step (ow : List X.toCombMap.Dart) (s t : ℕ) (ht : t + 1 < (ow.rotate s).length)
    (hp : (t + s) % ow.length < ow.length)
    (h : X.toCombMap.facePerm (ow[(t + s) % ow.length]'hp) =
      ow[((t + s) % ow.length + 1) % ow.length]'(Nat.mod_lt _
        (Nat.lt_of_le_of_lt (Nat.zero_le _) hp))) :
    X.toCombMap.facePerm ((ow.rotate s)[t]'(by omega)) = (ow.rotate s)[t + 1]'ht := by
  rw [List.getElem_rotate, List.getElem_rotate]
  exact h.trans (PocketRun.getElem_idx_congr ow
    (by rw [Nat.mod_add_mod, Nat.add_right_comm t s 1]) _ _)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.ArcClose.rotate_step

/-- **A block on a cell arc whose positions are kept or pinch-free is a face chain.** -/
theorem rotate_chain_step (E : EnclosedFaceSetSucc X F ow) (k : Fin X.rCellCount)
    (A : CyclicArc (cellDarts X k)) {s : ℕ} {u v : List X.toCombMap.Dart}
    (hs : ow.rotate s = u ++ v) (hu : ∀ x ∈ u, x ∈ A.darts)
    (hstep : ∀ (t : ℕ), t + 1 < u.length → ∀ (hp : (t + s) % ow.length < ow.length),
      walkKeep X.toCombMap ow (X.toCombMap.facePerm (ow[(t + s) % ow.length]'hp)) ∨
        PocketRun.PinchFreeAt X.toCombMap (ow[(t + s) % ow.length]'hp))
    (t : ℕ) (ht : t + 1 < u.length) :
    X.toCombMap.facePerm ((ow.rotate s)[t]'(lt_length_rotate hs (by omega))) =
      (ow.rotate s)[t + 1]'(lt_length_rotate hs ht) := by
  have hlt : t + 1 < ow.length := by
    have h1 := lt_length_rotate hs ht
    rw [List.length_rotate] at h1
    exact h1
  have hp : (t + s) % ow.length < ow.length := Nat.mod_lt _ (by omega)
  have h0 := hu _ (mem_of_rotate hs t (by omega) hp)
  have h1 := hu _ (mem_of_rotate_succ hs t ht hp)
  exact rotate_step ow s t (lt_length_rotate hs ht) hp
    (step_of_keep_or_pinch E _ hp (hstep t ht hp)
      ((PocketRun.arcFaceOf k A h1).trans (PocketRun.arcFaceOf k A h0).symm))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.ArcClose.rotate_chain_step

/-- **Such a block is a sub-arc.** -/
theorem exists_cellArc_of_rotate (E : EnclosedFaceSetSucc X F ow) (k : Fin X.rCellCount)
    (A : CyclicArc (cellDarts X k)) {s : ℕ} {u v : List X.toCombMap.Dart}
    (hs : ow.rotate s = u ++ v) (hu : ∀ x ∈ u, x ∈ A.darts)
    (hstep : ∀ (t : ℕ), t + 1 < u.length → ∀ (hp : (t + s) % ow.length < ow.length),
      walkKeep X.toCombMap ow (X.toCombMap.facePerm (ow[(t + s) % ow.length]'hp)) ∨
        PocketRun.PinchFreeAt X.toCombMap (ow[(t + s) % ow.length]'hp)) :
    ∃ B : CyclicArc (cellDarts X k), B.darts = u := by
  have hnd : (u ++ v).Nodup := by
    rw [← hs]
    exact List.nodup_rotate.mpr E.nodup
  refine PocketRun.exists_cellArc_of_isChain k A u (List.nodup_append.mp hnd).1 hu ?_
  intro t ht
  have h0 := lt_length_rotate hs (show t < u.length by omega)
  have h1 := lt_length_rotate hs ht
  have e0 : (ow.rotate s)[t]'h0 = u[t] :=
    (List.getElem_of_eq hs h0).trans (List.getElem_append_left (by omega))
  have e1 : (ow.rotate s)[t + 1]'h1 = u[t + 1] :=
    (List.getElem_of_eq hs h1).trans (List.getElem_append_left ht)
  rw [← e0, ← e1]
  exact rotate_chain_step E k A hs hu hstep t ht

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.ArcClose.exists_cellArc_of_rotate

end ArcClose

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
