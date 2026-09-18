import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.NoWalkAbsorbStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRunArc
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellWalk
import GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
import GroupApproximation.GGT.VanKampen.FaceSetBoundaryWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-35: local step clauses for a closed arc

Fix an enclosed walk `E : EnclosedFaceSetSucc X F ow` and a cell arc `A` of the cell `k`.  Call
`A` **closed** for `ow` when every `g ∈ A ∩ ow` with `facePerm g ∈ A` has `facePerm g ∈ ow`.

* `noWalkAbsorb_step_of_closed`: if `A` is closed and `ow` has a dart off `A`, the local step
  clause S1a holds for `A`.  At a junction `p` (`facePerm ow[p] ∉ A`) with `ow[p+1] ∈ A`, every
  position of `A` steps into `A`, so the whole walk lies on `A`.
* `noWalkAbsorb_unique_of_closed`: if `A` is closed and all of `ow` lies on `A`, the junction
  clause S1b holds (`PocketRun.eq_of_facePerm_not_mem` and `nodup`).
* `noWalkAbsorb_closed_of_sideFaces`: for `F = sideFaces w`, a list `l` with `invDarts l ⊆ w` is
  closed.
* `noWalkAbsorb_mem_walk_of_first`, `_of_second`: `invDarts G₁ ⊆ K.walk` and `invDarts G₂ ⊆ K.walk`.
* `noWalkAbsorb_walkKeep_alpha_of_sideFaces`: for `F = sideFaces w`, a walk dart with an `F` face
  across has `walkKeep w (α d)`.  Otherwise its own face would be in `F`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded SimpleClosedWalkSides

namespace FourPieceWitness

section Closed

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {X : DiscDiagram.{u, w, v} W} {F : Finset X.toCombMap.Face} {ow : List X.toCombMap.Dart}

/-- **S1a for a closed arc.** -/
theorem noWalkAbsorb_step_of_closed (E : EnclosedFaceSetSucc X F ow) (k : Fin X.rCellCount)
    (A : CyclicArc (cellDarts X k))
    (hclosed : ∀ g ∈ A.darts, g ∈ ow → X.toCombMap.facePerm g ∈ A.darts →
      X.toCombMap.facePerm g ∈ ow)
    (hoff : ∃ d ∈ ow, d ∉ A.darts) :
    ∀ (p : ℕ) (hp : p < ow.length), ow[p] ∈ A.darts →
      ow[(p + 1) % ow.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le p) hp)) ∈ A.darts →
      walkKeep X.toCombMap ow (X.toCombMap.facePerm ow[p]) ∨
        PocketRun.PinchFreeAt X.toCombMap ow[p] := by
  intro p hp hmp hmp1
  by_cases hfp : X.toCombMap.facePerm ow[p] ∈ A.darts
  · exact Or.inl (Or.inl (hclosed _ hmp (List.getElem_mem hp) hfp))
  · exfalso
    have hlen : 0 < ow.length := Nat.lt_of_le_of_lt (Nat.zero_le p) hp
    have hsucc : ∀ (q : ℕ) (hq : q < ow.length), ow[q] ∈ A.darts →
        ow[(q + 1) % ow.length]'(Nat.mod_lt _ hlen) ∈ A.darts := by
      intro q hq hmq
      by_cases hfq : X.toCombMap.facePerm ow[q] ∈ A.darts
      · have h1 := PocketRun.succ_eq_facePerm_of_keep E q hq
          (Or.inl (hclosed _ hmq (List.getElem_mem hq) hfq))
        rw [h1] at hfq
        exact hfq
      · have hqp : q = p := (List.Nodup.getElem_inj_iff E.nodup).mp
          (PocketRun.eq_of_facePerm_not_mem (X.faceBoundary (Embedded.cell X k).face) A hmq hmp
            hfq hfp)
        have h2 : ow[(q + 1) % ow.length]'(Nat.mod_lt _ hlen) =
            ow[(p + 1) % ow.length]'(Nat.mod_lt _ hlen) :=
          PocketRun.getElem_idx_congr ow (by rw [hqp]) _ _
        rw [h2]
        exact hmp1
    have hall : ∀ (n : ℕ) (hn : (p + n) % ow.length < ow.length),
        ow[(p + n) % ow.length]'hn ∈ A.darts := by
      intro n
      induction n with
      | zero =>
        intro hn
        have h0 : ow[(p + 0) % ow.length]'hn = ow[p]'hp :=
          PocketRun.getElem_idx_congr ow (by rw [Nat.add_zero, Nat.mod_eq_of_lt hp]) hn hp
        rw [h0]
        exact hmp
      | succ r ih =>
        intro hn
        have h1 := hsucc ((p + r) % ow.length) (Nat.mod_lt _ hlen) (ih (Nat.mod_lt _ hlen))
        have h2 : ow[((p + r) % ow.length + 1) % ow.length]'(Nat.mod_lt _ hlen) =
            ow[(p + (r + 1)) % ow.length]'hn :=
          PocketRun.getElem_idx_congr ow (by rw [Nat.mod_add_mod, Nat.add_assoc]) _ _
        rw [← h2]
        exact h1
    obtain ⟨d, hd, hnd⟩ := hoff
    obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem hd
    have h3 := hall (r + ow.length - p) (Nat.mod_lt _ hlen)
    have h4 : ow[(p + (r + ow.length - p)) % ow.length]'(Nat.mod_lt _ hlen) = ow[r]'hr :=
      PocketRun.getElem_idx_congr ow (by
        rw [show p + (r + ow.length - p) = r + ow.length by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt hr]) _ _
    rw [h4] at h3
    exact hnd h3

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.noWalkAbsorb_step_of_closed

/-- **S1b for a closed arc.** -/
theorem noWalkAbsorb_unique_of_closed (E : EnclosedFaceSetSucc X F ow) (k : Fin X.rCellCount)
    (A : CyclicArc (cellDarts X k))
    (hclosed : ∀ g ∈ A.darts, g ∈ ow → X.toCombMap.facePerm g ∈ A.darts →
      X.toCombMap.facePerm g ∈ ow)
    (hall : ∀ d ∈ ow, d ∈ A.darts) :
    ∀ (p q : ℕ) (hp : p < ow.length) (hq : q < ow.length),
      ¬ (walkKeep X.toCombMap ow (X.toCombMap.facePerm ow[p]) ∨
        PocketRun.PinchFreeAt X.toCombMap ow[p]) →
      ¬ (walkKeep X.toCombMap ow (X.toCombMap.facePerm ow[q]) ∨
        PocketRun.PinchFreeAt X.toCombMap ow[q]) → p = q := by
  intro p q hp hq hnp hnq
  have hjunc : ∀ (s : ℕ) (hs : s < ow.length),
      ¬ (walkKeep X.toCombMap ow (X.toCombMap.facePerm ow[s]) ∨
        PocketRun.PinchFreeAt X.toCombMap ow[s]) → X.toCombMap.facePerm ow[s] ∉ A.darts :=
    fun s hs hns hf => hns (Or.inl (Or.inl (hclosed _ (hall _ (List.getElem_mem hs))
      (List.getElem_mem hs) hf)))
  exact (List.Nodup.getElem_inj_iff E.nodup).mp
    (PocketRun.eq_of_facePerm_not_mem (X.faceBoundary (Embedded.cell X k).face) A
      (hall _ (List.getElem_mem hp)) (hall _ (List.getElem_mem hq)) (hjunc p hp hnp)
      (hjunc q hq hnq))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.noWalkAbsorb_unique_of_closed
