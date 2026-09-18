import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceArcCloseArc
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-44: block-local forms of the arc-closing lemmas

These are block-local versions of `ArcClose.arc_of_block` and `ArcClose.arc_of_all`
(`FourPieceArcCloseArc.lean`, lane gl-p07-26).  They are the engine of
`witnessArcsBlocks` (`WitnessArcsBlocksProof.lean`).

## Proof route

* `witnessArcsBlocks_getElem_rotate`: if `ow.rotate s = u ++ v` and `t < |u|`, then
  `ow[(t + s) % |ow|] = u[t]` (`List.getElem_rotate`).
* `witnessArcsBlocks_arc_of_block`: this copies the proof of `ArcClose.arc_of_block`.  The walk
  order block `invDarts U` is a rotation prefix of `ow`.  Its non-final entries are the entries of
  `(invDarts U).dropLast` (`List.getElem_dropLast`), which are good by hypothesis.  So
  `ArcClose.exists_cellArc_of_rotate` applies.
* `witnessArcsBlocks_arc_of_all`: `ArcClose.arc_of_all`, with the junction uniqueness obtained
  from uniqueness of bad darts and `E.nodup` (`List.Nodup.getElem_inj_iff`).
* `witnessArcsBlocks_mem_of_dropLast`: an entry of `(invDarts U).dropLast` for a block
  `U ⊆ invDarts A.darts` lies on `A`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded SimpleClosedWalkSides

/-- **The block entry at a rotated position.** -/
theorem witnessArcsBlocks_getElem_rotate {α : Type*} {ow u v : List α} {s : ℕ}
    (hs : ow.rotate s = u ++ v) (t : ℕ) (ht : t < u.length)
    (hp : (t + s) % ow.length < ow.length) :
    ow[(t + s) % ow.length]'hp = u[t] :=
  (List.getElem_rotate ow s t (ArcClose.lt_length_rotate hs ht)).symm.trans
    ((List.getElem_of_eq hs (ArcClose.lt_length_rotate hs ht)).trans
      (List.getElem_append_left ht))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessArcsBlocks_getElem_rotate

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {X : DiscDiagram.{u, w, v} W} {F : Finset X.toCombMap.Face} {ow : List X.toCombMap.Dart}

/-- **A non-final walk-order entry of a block on an arc lies on the arc.** -/
theorem witnessArcsBlocks_mem_of_dropLast {cyc : List X.toCombMap.Dart} (A : CyclicArc cyc)
    {U : List X.toCombMap.Dart} (hU : ∀ e ∈ U, e ∈ invDarts X A.darts)
    {x : X.toCombMap.Dart} (hx : x ∈ (invDarts X U).dropLast) : x ∈ A.darts := by
  have h1 := hU _ ((Embedded.mem_invDarts_iff U x).mp (List.dropLast_subset _ hx))
  rw [Embedded.mem_invDarts_iff, X.toCombMap.alpha_involutive x] at h1
  exact h1

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessArcsBlocks_mem_of_dropLast

/-- **Clause 4a from block-local goodness.** -/
theorem witnessArcsBlocks_arc_of_block (E : EnclosedFaceSetSucc X F ow) (k : Fin X.rCellCount)
    (A : CyclicArc (cellDarts X k))
    {m : ℕ} {U V : List X.toCombMap.Dart} (hm : (invDarts X ow).rotate m = U ++ V)
    (hU : ∀ e ∈ U, e ∈ invDarts X A.darts)
    (hloc : ∀ x ∈ (invDarts X U).dropLast,
      walkKeep X.toCombMap ow (X.toCombMap.facePerm x) ∨ PocketRun.PinchFreeAt X.toCombMap x) :
    ∃ B : CyclicArc (cellDarts X k), U = invDarts X B.darts := by
  obtain ⟨r, hr⟩ := SideBound.exists_rotate_invDarts ow m
  have hr' : ow.rotate r = invDarts X V ++ invDarts X U := by
    rw [← Embedded.invDarts_invDarts (ow.rotate r), hr, hm, Embedded.invDarts_append]
  have hs : ow.rotate (r + (invDarts X V).length) = invDarts X U ++ invDarts X V := by
    rw [← List.rotate_rotate, hr', List.rotate_append_length_eq]
  have hu : ∀ x ∈ invDarts X U, x ∈ A.darts := by
    intro x hx
    have h1 := hU _ ((Embedded.mem_invDarts_iff U x).mp hx)
    rw [Embedded.mem_invDarts_iff, X.toCombMap.alpha_involutive x] at h1
    exact h1
  obtain ⟨B, hB⟩ := ArcClose.exists_cellArc_of_rotate E k A hs hu (fun t ht hp => by
    have e := witnessArcsBlocks_getElem_rotate hs t (by omega) hp
    rw [e]
    have hlt : t < (invDarts X U).dropLast.length := by
      rw [List.length_dropLast]
      omega
    have hmem := List.getElem_mem hlt
    rw [List.getElem_dropLast] at hmem
    exact hloc _ hmem)
  exact ⟨B, by rw [hB, Embedded.invDarts_invDarts]⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessArcsBlocks_arc_of_block

/-- **Clause 4b from uniqueness of the bad walk dart.** -/
theorem witnessArcsBlocks_arc_of_all (E : EnclosedFaceSetSucc X F ow) (k : Fin X.rCellCount)
    (A : CyclicArc (cellDarts X k)) (hall : ∀ e ∈ invDarts X ow, e ∈ invDarts X A.darts)
    (hone : ∀ x ∈ ow, ∀ y ∈ ow,
      ¬ (walkKeep X.toCombMap ow (X.toCombMap.facePerm x) ∨
        PocketRun.PinchFreeAt X.toCombMap x) →
      ¬ (walkKeep X.toCombMap ow (X.toCombMap.facePerm y) ∨
        PocketRun.PinchFreeAt X.toCombMap y) → x = y) :
    ∃ (n : ℕ) (B : CyclicArc (cellDarts X k)),
      invDarts X (ow.rotate n) = invDarts X B.darts :=
  ArcClose.arc_of_all E k A (ArcClose.all_mem_of_invDarts A hall) (fun p q hp hq hnp hnq =>
    (E.nodup.getElem_inj_iff).mp
      (hone _ (List.getElem_mem hp) _ (List.getElem_mem hq) hnp hnq))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.witnessArcsBlocks_arc_of_all

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
