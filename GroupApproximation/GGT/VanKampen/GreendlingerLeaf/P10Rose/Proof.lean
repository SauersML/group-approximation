import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.InPlaceFilter
import GroupApproximation.Meta.AxiomGuard

/-!
# The rose step: the endpoint module and its remaining gap

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  The endpoint `GreendlingerLeaf.P10Rose.rose :
P10ChordLift.RoseStepStatement.{u, w, v}` belongs to this module (it is imported by
`Piece10/Proof`).  The earlier contents of this module (`zeroArc`, `ofLobe`, `exists_step_of_cut`
and its side variants, `RoseCombinatorialStepStatement`, `rose_of_combinatorialStep`) now live in
`P10Rose/Cut`, with unchanged names; the in-place constructors live in `P10Rose/InPlace`.

* `RoseInPlaceStepStatement` (OPEN): the rose step inside the same diagram.
* `combinatorialStep_of_inPlaceStep`: `RoseCombinatorialStepStatement` from it, with `X' = X`.
* `rose_of_inPlaceStep`: `P10ChordLift.RoseStepStatement` from it.
* `inPlaceStep_of_filterStep`, `rose_of_filterStep`: both from `RoseFilterStepStatement` (module
  `P10Rose/InPlaceFilter`), the isolated remaining claim: a face set whose boundary is the old cycle
  filtered by a predicate keeping both arcs, in walk order, with a shared vertex.

## Plan for the gap

Write `c = K.boundary.cycle`, `F = K.faces`, and call the classes of the face relation
`FaceClassStep (walkKeep c)` *regions*; each edge of `c` has `F` on exactly one side, so regions are
`F`-regions or non-`F` regions, and the exterior region `E` contains the exterior face.  At a vertex
`v` visited `k` times the rotation reads `o_1 S_1 ī_1 T_1 … o_k S_k ī_k T_k` (outgoing darts, non-`F`
sectors, reversed incoming darts, `F` sectors); a passage is `ī_a → o_{π a}`, a first turn is
`π a = a`, and the rose hypothesis forbids `π a = a + 1` (an uncrossed non-first turn), so `k = 2`
forces `π = id` and `k = 3` forces `π = id` or `a ↦ a - 1`.

1. **A lake other than the source lake.**  Fill it (`step_of_faces` with `F' = F ∪ lake`): its
   boundary darts are removed from `c`, each maximal run of them is a sub-walk from a vertex back to
   itself (the lake meets the rest of the walk only at vertices where the passages cross), the arcs
   stay, the sides shrink, and a vertex of the lake is shared with a kept dart by connectivity.
2. **Otherwise**, an `F`-region `B` not containing the kept cell, or the region containing it, is a
   lobe: remove the other regions (`step_of_lobe`).  The expected reason a proper lobe exists here:
   with no lake besides the source lake, a pinched vertex lies on two distinct `F`-regions (for
   `k ≥ 2` sectors of one region and of `E` cannot alternate around `v`).

The open points are (a) the walk-order claim in both cases, that the surviving boundary darts, in
the order inherited from `c`, form a closed walk around the arcs, and (b) the existence claim of
step 2.  Both use planarity (non-interleaving of regions around a vertex) and are not yet
formalised.  Filling all lakes at once (`step_of_absorb`) is not enough, and neither is a lobe: see
the two-hole example in the docstring of `P10Rose/InPlace`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides

/-- **The rose step in place** (OPEN; the remaining gap of `P10Rose`).  Under the hypotheses of
`RoseCombinatorialStepStatement`, some pocket face set of the same diagram is in walk order, has
proper arcs and strictly fewer repeated visits.  Its intended proof chooses a new face set and
applies `step_of_faces`, `step_of_lobe` or `step_of_absorb` (module `P10Rose/InPlace`). -/
def RoseInPlaceStepStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda) (eps : ℕ) (X : DiscDiagram.{u, w, v} W) (lo hi : ℕ), X.LeastArea →
    (∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d)) →
    ∀ K : PocketFaceSet D eps X lo hi, K.ClosedWalk → ¬ K.FirstTurns →
      K.sourceArc.length < (cellDarts X K.source).length →
      K.targetArc.length < (outerDarts X).length →
      ¬Unpinched X.toCombMap K.faces →
      P10ChordLift.AllNonFirstTurnsCrossed K →
        ∃ K' : PocketFaceSet D eps X lo hi, K'.ClosedWalk ∧
          K'.sourceArc.length < (cellDarts X K'.source).length ∧
          K'.targetArc.length < (outerDarts X).length ∧
          K'.repeatedVisits < K.repeatedVisits

/-- **The combinatorial rose step from the in-place one**, keeping the diagram. -/
theorem combinatorialStep_of_inPlaceStep (h : RoseInPlaceStepStatement.{u, w, v}) :
    RoseCombinatorialStepStatement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨K', hK', hsrc', htgt', hlt⟩ :=
    h D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  exact ⟨X, K', ⟨OEquivalentDiscDiagram.refl X⟩, hlabel, hK', hsrc', htgt', hlt⟩

/-- **The rose step from the in-place one.** -/
theorem rose_of_inPlaceStep (h : RoseInPlaceStepStatement.{u, w, v}) :
    P10ChordLift.RoseStepStatement.{u, w, v} :=
  rose_of_combinatorialStep (combinatorialStep_of_inPlaceStep h)

/-- **The in-place rose step from the filter step**, by `step_of_filter`. -/
theorem inPlaceStep_of_filterStep (h : RoseFilterStepStatement.{u, w, v}) :
    RoseInPlaceStepStatement.{u, w, v} := by
  intro G _ Lambda W D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  obtain ⟨faces, kept, p, hout, hsource, hkept, hbd, ht₁, ht₂, hwalk, x, hx, y, hy, hpx, hpy,
    hxy⟩ := h D eps X lo hi hlea hlabel K hK hnft hsrc htgt hpinch hrose
  exact step_of_filter K hlabel hsrc htgt hout hsource hkept p hbd ht₁ ht₂ hwalk hx hpx hy hpy hxy

/-- **The rose step from the filter step.** -/
theorem rose_of_filterStep (h : RoseFilterStepStatement.{u, w, v}) :
    P10ChordLift.RoseStepStatement.{u, w, v} :=
  rose_of_inPlaceStep (inPlaceStep_of_filterStep h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.RoseInPlaceStepStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.combinatorialStep_of_inPlaceStep
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.rose_of_inPlaceStep
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.inPlaceStep_of_filterStep
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10Rose.rose_of_filterStep
