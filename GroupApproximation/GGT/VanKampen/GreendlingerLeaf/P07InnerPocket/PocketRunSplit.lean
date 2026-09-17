import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRunArc
import GroupApproximation.Meta.AxiomGuard

/-!
# Runs follow their piece: a run is at most two sub-arcs (lane `gl-p07-09`)

Let `E : EnclosedFaceSetSucc X F w` with `w = u ++ v`.  Let `A` be an arc of the cell `k` whose
darts are all walk darts, and suppose every dart of the block `u` is a dart of `A`.

* `facePerm_run_step`: take `t + 1 < |u|`.  If `facePerm u[t]` is a dart of `A`, then it is a walk
  dart, so `succ_eq_facePerm` (keep case) gives `facePerm u[t] = u[t+1]`.  If instead `u[t]` is
  pinch-free, then `u[t+1]` and `u[t]` both lie on the face of cell `k` and the pinch case applies.
* `junction_unique`: `u` has no repeated dart (it is a block of `w`).  Among the darts of `A`, only
  one has its `facePerm` outside `A` (`eq_of_facePerm_not_mem`).  So there is at most one index `t₀`
  of `u` with `facePerm u[t₀] ∉ A`.
* `exists_two_cellArc_of_steps`: if there is no junction, `u` is a chain, so it is an arc, and the
  second piece is empty.  Otherwise split `u` after `t₀`.  Both halves are chains, because every
  step inside them is at an index `≠ t₀`.
* `exists_two_cyclicArc_of_run`: every run is at most two sub-arcs.
* `exists_cyclicArc_of_run`: if the junction dart (if any) is pinch-free, the run is one sub-arc.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121) through Osin's Lemma 9.7 (the inner pocket); certifies no
printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

open Embedded SimpleClosedWalkSides

universe u w v

namespace PocketRun

/-- The empty arc of a cycle. -/
def emptyArc {α : Type*} (cyc : List α) : CyclicArc cyc := ⟨0, 0, Nat.zero_le _⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRun.emptyArc

theorem emptyArc_darts {α : Type*} (cyc : List α) : (emptyArc cyc).darts = [] := List.take_zero

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRun.emptyArc_darts

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {X : DiscDiagram.{u, w, v} W} {F : Finset X.toCombMap.Face} {ow : List X.toCombMap.Dart}

/-- Arc darts of a cell lie on the face of that cell. -/
theorem arcFaceOf (k : Fin X.rCellCount) (A : CyclicArc (cellDarts X k)) {x : X.toCombMap.Dart}
    (hx : x ∈ A.darts) : X.toCombMap.faceOf x = (cell X k).face :=
  ((X.faceBoundary (cell X k).face).mem_iff x).mp (A.mem_cycle_of_mem_darts hx)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRun.arcFaceOf

/-- A duplicate-free face chain of arc darts is a sub-arc. -/
theorem exists_cellArc_of_isChain (k : Fin X.rCellCount) (A : CyclicArc (cellDarts X k))
    (u : List X.toCombMap.Dart) (hnd : u.Nodup) (hu : ∀ x ∈ u, x ∈ A.darts)
    (hchain : ∀ (t : ℕ) (ht : t + 1 < u.length), X.toCombMap.facePerm u[t] = u[t + 1]) :
    ∃ B : CyclicArc (cellDarts X k), B.darts = u :=
  exists_cyclicArc_of_isChain (X.faceBoundary (cell X k).face) u hnd
    (fun x hx => A.mem_cycle_of_mem_darts (hu x hx)) (List.isChain_iff_getElem.mpr hchain)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRun.exists_cellArc_of_isChain

/-- **At most one junction.** -/
theorem junction_unique (k : Fin X.rCellCount) (A : CyclicArc (cellDarts X k))
    {u : List X.toCombMap.Dart} (hnd : u.Nodup) (hu : ∀ x ∈ u, x ∈ A.darts) {s t : ℕ}
    (hs : s < u.length) (ht : t < u.length) (hfs : X.toCombMap.facePerm u[s] ∉ A.darts)
    (hft : X.toCombMap.facePerm u[t] ∉ A.darts) : s = t :=
  (List.Nodup.getElem_inj_iff hnd).mp
    (eq_of_facePerm_not_mem (X.faceBoundary (cell X k).face) A (hu _ (List.getElem_mem hs))
      (hu _ (List.getElem_mem ht)) hfs hft)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRun.junction_unique

/-- **Steps inside the arc give at most two sub-arcs.** -/
theorem exists_two_cellArc_of_steps (k : Fin X.rCellCount) (A : CyclicArc (cellDarts X k))
    (u : List X.toCombMap.Dart) (hnd : u.Nodup) (hu : ∀ x ∈ u, x ∈ A.darts)
    (hstep : ∀ (t : ℕ) (ht : t + 1 < u.length), X.toCombMap.facePerm u[t] ∈ A.darts →
      X.toCombMap.facePerm u[t] = u[t + 1]) :
    ∃ B₁ B₂ : CyclicArc (cellDarts X k), u = B₁.darts ++ B₂.darts := by
  by_cases hj : ∃ (t₀ : ℕ) (h₀ : t₀ < u.length), X.toCombMap.facePerm u[t₀] ∉ A.darts
  · obtain ⟨t₀, h₀, hf₀⟩ := hj
    have hmem : ∀ (t : ℕ) (ht : t < u.length), t ≠ t₀ → X.toCombMap.facePerm u[t] ∈ A.darts := by
      intro t ht hne
      by_contra hf
      exact hne (junction_unique k A hnd hu ht h₀ hf hf₀)
    obtain ⟨B₁, hB₁⟩ := exists_cellArc_of_isChain k A (u.take (t₀ + 1))
      (hnd.sublist (List.take_sublist _ _)) (fun x hx => hu x (List.mem_of_mem_take hx)) (by
        intro t ht
        have hlt : t + 1 < u.length := by rw [List.length_take] at ht; omega
        have hlt₀ : t + 1 < t₀ + 1 := by rw [List.length_take] at ht; omega
        rw [List.getElem_take, List.getElem_take]
        exact hstep t hlt (hmem t (by omega) (by omega)))
    obtain ⟨B₂, hB₂⟩ := exists_cellArc_of_isChain k A (u.drop (t₀ + 1))
      (hnd.sublist (List.drop_sublist _ _)) (fun x hx => hu x (List.mem_of_mem_drop hx)) (by
        intro j hjl
        have hlt : t₀ + 1 + j + 1 < u.length := by rw [List.length_drop] at hjl; omega
        rw [List.getElem_drop, List.getElem_drop]
        exact (hstep (t₀ + 1 + j) hlt (hmem _ (by omega) (by omega))).trans
          (getElem_idx_congr u (Nat.add_assoc (t₀ + 1) j 1) _ _))
    exact ⟨B₁, B₂, by rw [hB₁, hB₂, List.take_append_drop]⟩
  · obtain ⟨B₁, hB₁⟩ := exists_cellArc_of_isChain k A u hnd hu (fun t ht =>
      hstep t ht (by
        by_contra hf
        exact hj ⟨t, by omega, hf⟩))
    exact ⟨B₁, emptyArc _, by rw [hB₁, emptyArc_darts, List.append_nil]⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRun.exists_two_cellArc_of_steps

/-- A block of the walk has no repeated dart. -/
theorem run_nodup (E : EnclosedFaceSetSucc X F ow) {u v : List X.toCombMap.Dart}
    (hw : ow = u ++ v) : u.Nodup := by
  subst hw
  exact (List.nodup_append.mp E.nodup).1

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRun.run_nodup

/-- **One step of a run.** -/
theorem facePerm_run_step (E : EnclosedFaceSetSucc X F ow) {u v : List X.toCombMap.Dart}
    (hw : ow = u ++ v) (k : Fin X.rCellCount) (A : CyclicArc (cellDarts X k))
    (hAw : ∀ x ∈ A.darts, x ∈ ow) (hu : ∀ x ∈ u, x ∈ A.darts) (t : ℕ) (ht : t + 1 < u.length)
    (h : X.toCombMap.facePerm u[t] ∈ A.darts ∨ PinchFreeAt X.toCombMap u[t]) :
    X.toCombMap.facePerm u[t] = u[t + 1] := by
  subst hw
  have hlt : t + 1 < (u ++ v).length := by rw [List.length_append]; omega
  have hg0 : (u ++ v)[t]'(by omega) = u[t]'(by omega) := List.getElem_append_left (by omega)
  have hg1 : (u ++ v)[t + 1]'hlt = u[t + 1] := List.getElem_append_left ht
  have hstep := succ_eq_facePerm E t hlt (by
    rw [hg0, hg1]
    rcases h with hmem | hpinch
    · exact Or.inl (Or.inl (hAw _ hmem))
    · exact Or.inr ⟨hpinch, (arcFaceOf k A (hu _ (List.getElem_mem ht))).trans
        (arcFaceOf k A (hu _ (List.getElem_mem (by omega)))).symm⟩)
  rw [hg0, hg1] at hstep
  exact hstep

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRun.facePerm_run_step

/-- **Every run is at most two sub-arcs.** -/
theorem exists_two_cyclicArc_of_run (E : EnclosedFaceSetSucc X F ow) {u v : List X.toCombMap.Dart}
    (hw : ow = u ++ v) (k : Fin X.rCellCount) (A : CyclicArc (cellDarts X k))
    (hAw : ∀ x ∈ A.darts, x ∈ ow) (hu : ∀ x ∈ u, x ∈ A.darts) :
    ∃ B₁ B₂ : CyclicArc (cellDarts X k), u = B₁.darts ++ B₂.darts :=
  exists_two_cellArc_of_steps k A u (run_nodup E hw) hu
    (fun t ht hmem => facePerm_run_step E hw k A hAw hu t ht (Or.inl hmem))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRun.exists_two_cyclicArc_of_run

/-- **A run with a pinch-free junction is one sub-arc.** -/
theorem exists_cyclicArc_of_run (E : EnclosedFaceSetSucc X F ow) {u v : List X.toCombMap.Dart}
    (hw : ow = u ++ v) (k : Fin X.rCellCount) (A : CyclicArc (cellDarts X k))
    (hAw : ∀ x ∈ A.darts, x ∈ ow) (hu : ∀ x ∈ u, x ∈ A.darts)
    (hpinch : ∀ x ∈ u, X.toCombMap.facePerm x ∉ A.darts → PinchFreeAt X.toCombMap x) :
    ∃ B : CyclicArc (cellDarts X k), B.darts = u :=
  exists_cellArc_of_isChain k A u (run_nodup E hw) hu (fun t ht =>
    facePerm_run_step E hw k A hAw hu t ht
      ((Classical.em (X.toCombMap.facePerm u[t] ∈ A.darts)).elim Or.inl
      (fun hmem => Or.inr (hpinch _ (List.getElem_mem (by omega)) hmem))))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRun.exists_cyclicArc_of_run

end PocketRun

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
