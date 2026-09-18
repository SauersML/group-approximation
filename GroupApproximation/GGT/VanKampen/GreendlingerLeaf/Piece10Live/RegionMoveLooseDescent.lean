import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.RegionMoveLooseDescentCount
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.RegionMoveLooseDescentConcl
import GroupApproximation.Meta.AxiomGuard

/-!
# Descent on the loose count

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  Lane gl-p10-24, idea (b).

## Route

* `RegionMoveLooseDescentPremises K`: the pocket premises of `RegionMoveCoreCloseStatement`.
* `RegionMoveLooseDescentSurgeryStatement` (OPEN; LOUD: EQUIVALENT to Close): for a pocket `K`
  satisfying the premises, either the conclusion holds for `K`, or some pocket `K'` with the same
  `D, ε, X, lo, hi` satisfies the premises, has a strictly smaller loose count, and its
  conclusion gives the conclusion for `K`.
* `regionMoveLooseDescent_close_of_surgery` (proved): Surgery → `RegionMoveCoreCloseStatement`,
  by strong induction on the loose count.
* `RegionMoveLooseDescentReorderStatement` (OPEN; LOUD: EQUIVALENT to Close): the surgery with
  `K'.faces = K.faces` in place of the transfer clause.  The transfer then always holds
  (`regionMoveLooseDescent_concl_of_faces_eq`), which gives
  `regionMoveLooseDescent_surgery_of_reorder` (proved).
* `regionMoveLooseDescent_surgery_of_close`, `regionMoveLooseDescent_reorder_of_close` (proved):
  truth certificates, through the left disjunct.

## Status (LOUD)

Both Statements are **logically equivalent** to `RegionMoveCoreCloseStatement`, and so to
`RegionMoveLooseSideStatement` and `RoseExtremalCoreStatement`.  They are true exactly when Close
is true.  The descent does **not** reduce the problem to the vacuous case.  Where there is a loose
crossing, the loose count is at least `3` (`regionMoveLooseDescent_three_le_count`), and a pocket
with loose count at most `1` has no loose crossing
(`regionMoveLooseDescent_not_looseCross_of_count_le_one`).  So at the floor, count `3`, a proof
of the surgery must take the left disjunct, which is Close itself.

## Truth check (scratchpad `gl-p10-24/model.py`)

The model has one vertex: bits on the corners of the rotation, excursion chords that do not cross,
and walk pairings whose composite is a single cycle.  These are the local configurations of a
pocket that are rose and in walk order.

* **The literal surgery is refuted.**  Exchanging the successors of two passages always splits the
  walk into two cycles, by parity: 27940 of 27940 tries at `n = 10`, 944082 of 944082 at `n = 12`.
  So `K'` can never come from a two-passage exchange that stays one closed walk.
* A three-passage rotation can keep one cycle.  It lowers the loose count while staying rose in
  only 1193 of 4862 rose configurations at `n = 10`, or 55075 of 108470 at `n = 12`.  Any
  single-cycle re-pairing at the vertex does so in only 1272 of 4862, or 58535 of 108470.
* No rose configuration with loose count `3` can descend while staying rose.  That is forced by
  the floor: 2884 configurations at `n = 10` and 31124 at `n = 12`.  Configurations with no
  descending re-pairing also occur above the floor: 690 of 1666 at count `4` and 16 of 312 at
  count `5` (`n = 10`).

So the surgery holds only where Close already holds.  Everything proved here is true outright.  The
two Statements are as plausible as Close: no counterexample is known.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove
open scoped Classical

section Pocket

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **The pocket premises of the core at a loose crossing.** -/
def RegionMoveLooseDescentPremises (K : PocketFaceSet D eps X lo hi) : Prop :=
  K.ClosedWalk ∧ ¬ K.FirstTurns ∧ K.sourceArc.length < (cellDarts X K.source).length ∧
    K.targetArc.length < (outerDarts X).length ∧ ¬Unpinched X.toCombMap K.faces ∧
    P10ChordLift.AllNonFirstTurnsCrossed K ∧ RegionMoveCoreCloseLooseCross K

/-- **The premises put the loose count at least `3`.** -/
theorem regionMoveLooseDescent_three_le_count_of_premises (K : PocketFaceSet D eps X lo hi)
    (hP : RegionMoveLooseDescentPremises K) : 3 ≤ RegionMoveLooseDescentCount K := by
  obtain ⟨hK, -, -, -, -, -, hloose⟩ := hP
  exact regionMoveLooseDescent_three_le_count K hK hloose

end Pocket

/-- **The loose-count surgery** (OPEN; LOUD: logically EQUIVALENT to
`RegionMoveCoreCloseStatement`, and as plausible).  A pocket satisfying the premises either
satisfies the conclusion, or has a pocket `K'` over the same `D, ε, X, lo, hi` that satisfies the
premises, has a strictly smaller loose count, and whose conclusion gives the conclusion for `K`.
At loose count `3`, the floor, only the left disjunct is available. -/
def RegionMoveLooseDescentSurgeryStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ), X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, RegionMoveLooseDescentPremises K →
      3 ≤ RegionMoveLooseDescentCount K →
      RegionMoveLooseDescentConcl K ∨
        ∃ K' : PocketFaceSet D eps X lo hi, RegionMoveLooseDescentPremises K' ∧
          RegionMoveLooseDescentCount K' < RegionMoveLooseDescentCount K ∧
          (RegionMoveLooseDescentConcl K' → RegionMoveLooseDescentConcl K)

/-- **The reordering surgery** (OPEN; LOUD: logically EQUIVALENT to
`RegionMoveCoreCloseStatement`): the surgery in which `K'` has the faces of `K`, so that only the
boundary walk is reordered. -/
def RegionMoveLooseDescentReorderStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ), X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, RegionMoveLooseDescentPremises K →
      3 ≤ RegionMoveLooseDescentCount K →
      RegionMoveLooseDescentConcl K ∨
        ∃ K' : PocketFaceSet D eps X lo hi, K'.faces = K.faces ∧
          RegionMoveLooseDescentPremises K' ∧
          RegionMoveLooseDescentCount K' < RegionMoveLooseDescentCount K

/-- **Close from the surgery**, by strong induction on the loose count. -/
theorem regionMoveLooseDescent_close_of_surgery
    (h : RegionMoveLooseDescentSurgeryStatement.{u, w, v}) :
    RegionMoveCoreCloseStatement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hlea hlabel
  have key : ∀ (n : ℕ) (K : PocketFaceSet D eps X lo hi), RegionMoveLooseDescentCount K = n →
      RegionMoveLooseDescentPremises K → RegionMoveLooseDescentConcl K := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro K hn hP
      rcases h D eps X lo hi hlea hlabel K hP
          (regionMoveLooseDescent_three_le_count_of_premises K hP) with
        hc | ⟨K', hP', hlt, himp⟩
      · exact hc
      · exact himp (ih (RegionMoveLooseDescentCount K') (lt_of_lt_of_eq hlt hn) K' rfl hP')
  intro K hK hnft hsrc htgt hpinch hrose hloose
  exact key _ K rfl ⟨hK, hnft, hsrc, htgt, hpinch, hrose, hloose⟩

/-- **The surgery from Close** (truth certificate, through the left disjunct). -/
theorem regionMoveLooseDescent_surgery_of_close (h : RegionMoveCoreCloseStatement.{u, w, v}) :
    RegionMoveLooseDescentSurgeryStatement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hlea hlabel K hP _
  obtain ⟨hK, hnft, hsrc, htgt, hpinch, hrose, hloose⟩ := hP
  exact Or.inl (h D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose hloose)

/-- **The surgery from the reordering surgery**: a pocket with the same faces transfers the
conclusion back (`regionMoveLooseDescent_concl_of_faces_eq`). -/
theorem regionMoveLooseDescent_surgery_of_reorder
    (h : RegionMoveLooseDescentReorderStatement.{u, w, v}) :
    RegionMoveLooseDescentSurgeryStatement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hlea hlabel K hP h3
  rcases h D eps X lo hi hlea hlabel K hP h3 with hc | ⟨K', hf, hP', hlt⟩
  · exact Or.inl hc
  · exact Or.inr ⟨K', hP', hlt, regionMoveLooseDescent_concl_of_faces_eq hf⟩

/-- **Close from the reordering surgery.** -/
theorem regionMoveLooseDescent_close_of_reorder
    (h : RegionMoveLooseDescentReorderStatement.{u, w, v}) :
    RegionMoveCoreCloseStatement.{u, w, v} :=
  regionMoveLooseDescent_close_of_surgery (regionMoveLooseDescent_surgery_of_reorder h)

/-- **The reordering surgery from Close** (truth certificate, through the left disjunct). -/
theorem regionMoveLooseDescent_reorder_of_close (h : RegionMoveCoreCloseStatement.{u, w, v}) :
    RegionMoveLooseDescentReorderStatement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hlea hlabel K hP _
  obtain ⟨hK, hnft, hsrc, htgt, hpinch, hrose, hloose⟩ := hP
  exact Or.inl (h D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose hloose)

/-- **The extremal-region core from the surgery.** -/
theorem regionMoveLooseDescent_extremalCore_of_surgery
    (h : RegionMoveLooseDescentSurgeryStatement.{u, w, v}) :
    RoseExtremalCoreStatement.{u, w, v} :=
  regionMoveCoreClose_extremalCore_of_close (regionMoveLooseDescent_close_of_surgery h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.RegionMoveLooseDescentPremises
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLooseDescent_three_le_count_of_premises
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.RegionMoveLooseDescentSurgeryStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.RegionMoveLooseDescentReorderStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLooseDescent_close_of_surgery
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLooseDescent_surgery_of_close
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLooseDescent_surgery_of_reorder
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLooseDescent_close_of_reorder
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLooseDescent_reorder_of_close
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLooseDescent_extremalCore_of_surgery
