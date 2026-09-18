import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceArcCloseStep
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.SideBoundCore
import GroupApproximation.GGT.VanKampen.FaceShelling
import GroupApproximation.GGT.VanKampen.FaceSetBoundaryWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-26: clause 4 of the corrected residual from local steps

This file derives clauses 4a and 4b of `PocketFourPieceArcAuditResidualStatement`
(`FourPieceArcAuditStatement.lean`) from local step clauses about positions of the walk.  Fix an
enclosed walk `E : EnclosedFaceSetSucc X F ow` and a cell arc `A` of the cell `k`.

## Proof route

* `ArcClose.arc_of_block` (clause 4a).  Suppose that at every position `p` where `ow[p]` and its
  successor both lie on `A`, `facePerm ow[p]` is kept or `ow[p]` is pinch-free.
  - `(invDarts ow).rotate m = U ++ V` is `invDarts (ow.rotate r)`
    (`SideBound.exists_rotate_invDarts`).
  - Inverting gives `ow.rotate r = invDarts V ++ invDarts U`, and rotating by `|invDarts V|` gives
    `invDarts U ++ invDarts V`.
  - The block `invDarts U` lies on `A`, so it is a sub-arc `B`
    (`ArcClose.exists_cellArc_of_rotate`).
  - Then `U = invDarts B.darts` (`Embedded.invDarts_invDarts`).
* `ArcClose.arc_of_all` (clause 4b).  Suppose every walk dart lies on `A` and at most one position
  is neither kept nor pinch-free.  Rotate past that junction `p₀`, or by `0` if there is none.
  Every other position is a step (`ArcClose.add_succ_mod_ne`), so the rotated walk is a sub-arc.
* `ArcClose.exists_not_mem_of_block` and `ArcClose.all_mem_of_invDarts` translate the hypotheses
  of clauses 4a and 4b about `invDarts` into statements about walk darts.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

universe u w v

open Embedded SimpleClosedWalkSides

namespace ArcClose

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {X : DiscDiagram.{u, w, v} W} {F : Finset X.toCombMap.Face} {ow : List X.toCombMap.Dart}

/-- **A block with an off-arc complement entry gives an off-arc walk dart.** -/
theorem exists_not_mem_of_block {cyc : List X.toCombMap.Dart} (A : CyclicArc cyc) {m : ℕ}
    {U V : List X.toCombMap.Dart} (hm : (invDarts X ow).rotate m = U ++ V)
    (hV : ∃ e ∈ V, e ∉ invDarts X A.darts) : ∃ d ∈ ow, d ∉ A.darts := by
  obtain ⟨e, he, hne⟩ := hV
  have h1 : e ∈ (invDarts X ow).rotate m := by
    rw [hm]
    exact List.mem_append.mpr (Or.inr he)
  exact ⟨X.toCombMap.alpha e, (Embedded.mem_invDarts_iff ow e).mp (List.mem_rotate.mp h1),
    fun h => hne ((Embedded.mem_invDarts_iff A.darts e).mpr h)⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.ArcClose.exists_not_mem_of_block

/-- **An all-arc inverse walk is an all-arc walk.** -/
theorem all_mem_of_invDarts {cyc : List X.toCombMap.Dart} (A : CyclicArc cyc)
    (h : ∀ e ∈ invDarts X ow, e ∈ invDarts X A.darts) : ∀ d ∈ ow, d ∈ A.darts := by
  intro d hd
  have h1 := h (X.toCombMap.alpha d) (by
    rw [Embedded.mem_invDarts_iff, X.toCombMap.alpha_involutive d]
    exact hd)
  rw [Embedded.mem_invDarts_iff, X.toCombMap.alpha_involutive d] at h1
  exact h1

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.ArcClose.all_mem_of_invDarts

/-- **Clause 4a from the local step clause.** -/
theorem arc_of_block (E : EnclosedFaceSetSucc X F ow) (k : Fin X.rCellCount)
    (A : CyclicArc (cellDarts X k))
    (hstep : ∀ (p : ℕ) (hp : p < ow.length), ow[p] ∈ A.darts →
      ow[(p + 1) % ow.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le p) hp)) ∈ A.darts →
      walkKeep X.toCombMap ow (X.toCombMap.facePerm ow[p]) ∨
        PocketRun.PinchFreeAt X.toCombMap ow[p])
    {m : ℕ} {U V : List X.toCombMap.Dart} (hm : (invDarts X ow).rotate m = U ++ V)
    (hU : ∀ e ∈ U, e ∈ invDarts X A.darts) :
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
  obtain ⟨B, hB⟩ := exists_cellArc_of_rotate E k A hs hu (fun t ht hp =>
    hstep _ hp (hu _ (mem_of_rotate hs t (by omega) hp)) (hu _ (mem_of_rotate_succ hs t ht hp)))
  exact ⟨B, by rw [hB, Embedded.invDarts_invDarts]⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.ArcClose.arc_of_block

/-- **Clause 4b from the local junction clause.** -/
theorem arc_of_all (E : EnclosedFaceSetSucc X F ow) (k : Fin X.rCellCount)
    (A : CyclicArc (cellDarts X k)) (hall : ∀ d ∈ ow, d ∈ A.darts)
    (huniq : ∀ (p q : ℕ) (hp : p < ow.length) (hq : q < ow.length),
      ¬ (walkKeep X.toCombMap ow (X.toCombMap.facePerm ow[p]) ∨
        PocketRun.PinchFreeAt X.toCombMap ow[p]) →
      ¬ (walkKeep X.toCombMap ow (X.toCombMap.facePerm ow[q]) ∨
        PocketRun.PinchFreeAt X.toCombMap ow[q]) → p = q) :
    ∃ (n : ℕ) (B : CyclicArc (cellDarts X k)),
      invDarts X (ow.rotate n) = invDarts X B.darts := by
  have hu : ∀ n, ∀ x ∈ ow.rotate n, x ∈ A.darts := fun _ x hx =>
    hall x (List.mem_rotate.mp hx)
  by_cases hj : ∃ (p₀ : ℕ) (h₀ : p₀ < ow.length),
      ¬ (walkKeep X.toCombMap ow (X.toCombMap.facePerm ow[p₀]) ∨
        PocketRun.PinchFreeAt X.toCombMap ow[p₀])
  · obtain ⟨p₀, h₀, hf₀⟩ := hj
    obtain ⟨B, hB⟩ := exists_cellArc_of_rotate (s := p₀ + 1) (u := ow.rotate (p₀ + 1))
      (v := []) E k A (List.append_nil _).symm (hu _) (fun t ht hp => by
        have hlt : t + 1 < ow.length := by
          rw [List.length_rotate] at ht
          exact ht
        by_contra hk
        exact add_succ_mod_ne hlt h₀ (huniq _ _ hp h₀ hk hf₀))
    exact ⟨p₀ + 1, B, by rw [hB]⟩
  · obtain ⟨B, hB⟩ := exists_cellArc_of_rotate (s := 0) (u := ow.rotate 0) (v := []) E k A
      (List.append_nil _).symm (hu _) (fun _ _ hp =>
        Classical.byContradiction fun hk => hj ⟨_, hp, hk⟩)
    exact ⟨0, B, by rw [hB]⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.ArcClose.arc_of_all

end ArcClose

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
