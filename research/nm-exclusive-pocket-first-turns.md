---
rg: 2
id: nm-exclusive-pocket-first-turns
kind: route
title: "Osin 9.7(b): take the pocket strictly between the two regions; it is in first-turn order, so the rose case never arises"
requires: []
---

**Status: OPEN route (paper argument, not formalized, not refereed).** Lane nm-switch-core, 2026-09-19.

## Source, pinned

D. Osin, *Small cancellations over relatively hyperbolic groups and embedding theorems*,
arXiv:math/0411039v3 (9 Jul 2011; Ann. of Math. 172 (2010) 1-39). This is reference [32] of Hull.
Section 9 is the Appendix, "The proof of Lemma 4.4". Lemma 9.7 is on p. 34, and the proof of (b) is on p. 35:

> "Let us consider the subdiagram Γ¹ of Δ such that: (i) ∂Γ¹ = s₁t₁s₂t₂, where s₁, s₂ are side
> arcs of some of Γ_{i,1}'s and t₁, t₂ are subpaths of ∂Π and the section q₁ of ∂Δ, respectively;
> (ii) Γ¹ contains all Γ_{i,1}'s."

The existence of Γ¹ is asserted without argument. Osin works under the convention of p. 8: 0-refinement
"enables us to assume that all diagrams [are] homeomorphic to a disc", citing Olshanskii's book, Ch. 4.
DGO (arXiv:1111.7048, §3) states the same convention and cites Olshanskii's book, §11. Osin also writes, p. 29:
"Lemma 4.4 (as well as Lemma 9.7) is, in fact, proved in [23]" and "all results of this section should be credited
to Olshanskii"
([23] = Olshanskii, IJAC 3 (1993), Lemma 6.6; p. 14 also cites an addendum in J. Algebra 226 (2000) 807-817).
That addendum has not been read yet.

## Why the formal rose case is an artifact

The formal producer (`PocketWalk.exists_of_exteriorAt`) takes Osin's *inclusive* Γ¹. The two extreme regions
lie inside the pocket, and s₁, s₂ are their *outer* sides. Across an outer side lies arbitrary diagram material,
so the pocket walk can take non-first turns, and the formal abstraction then allows crossed ones (the rose).
`IsNoncrossingClosedWalk` does not exclude this. It only asks that walk darts and reversed walk darts alternate
at each vertex, which every face-set boundary does.

## The route

Let x, y be the two exterior regions, and let F be the inclusive pocket. Set F⁻ = F \ (x ∪ y). Its boundary cycle
has four parts:
- the *inner* side of y (the side facing x);
- the gap arc of ∂Π between the source arcs of x and y (`CyclicArc.exists_spanArc`);
- the inner side of x;
- the arc of ∂Δ between the outer arcs of y and x.

**Claim.** This cycle is in first-turn order (`PocketFaceSet.FirstTurns`), provided:

- (R1) x and y have one corner-run at each vertex, for example disc regions, so that consecutive darts of a side
  turn around a single run of region faces;
- (R2) the source arcs and the outer arcs of x and y are nonempty.

**Proof sketch, turn by turn.** In each case the rotation from the out-dart meets only darts off the cycle before
it reaches the reversed in-dart.

- *Along the gap arc and the ∂Δ arc:* consecutive darts bound one corner of the face Π or of the outer face, so
  the rotation takes one step.
- *Along an inner side:* the rotation sweeps the single corner-run of the region (R1). The darts inside it lie on
  edges internal to the region, so none is on the cycle.
- *At a junction side → arc, on ∂Π:* the rotation passes the corner of Π, then the last edge of the region's
  source arc (region|Π, not a cycle edge), then the region's corner-run, and reaches the side's last dart (R2).
  The same holds with the outer face on ∂Δ.
- *At degenerate junctions (an empty side, gap arc or target arc):* the same sweep runs through two or three wall
  corners joined by shared edges.

**Consequence.** `PocketFaceSet.exists_simple_of_firstTurns` (landed, `Estimating/OsinPocketGoodCornersSection`)
gives a simple O-equivalent copy. `p10FM_QuadrantMoveStatement`, `p10LS_SelectionStatement` and the
2-connected switch-graph core are then never needed.

Osin's argument survives the exclusion of x and y:

- they carry no R-cells, so m₁ is unchanged;
- if m₁ = 0, Γ¹⁻ ∪ x ∪ y is the merged contiguity subdiagram;
- the inner sides are side arcs of length at most ε.

## Review items, settled on paper (2026-09-19, after bh-ref-t0 81a9ea634c)

1. **(R1)** holds automatically. `ContiguityGeometry.boundary` is a `FaceSetBoundary`. Its `BoundaryStep` is
   `facePerm` followed by internal moves, i.e. `BoundaryWalk`. Reversed, that is a first turn past
   region-internal darts (`ExclusiveTurns.firstTurn_of_boundaryWalk`). The inner sides are `y.rightSide` and
   `x.leftSide`; the landed inclusive producer uses the outer sides `y.leftSide`, `x.rightSide`.
2. **(R2), both arcs.** This is a field of the family: `RealizedSectionFamily.nondegenerate` says
   `0 < a.2.sourceArc.length ∧ 0 < a.2.targetArc.length` for every selected region, and
   `exteriorAt S.family i ⊆ S.family`. So target arcs are nonempty as well as source arcs.
3. **Regions carry no R-cell.** `ContiguityGeometry.innerGRegion hlea` (landed, `Estimating/OsinAppendixO52Prep`)
   has `cells_avoid`: at least area, no relator cell has its face in a region. The family's diagram is
   O-equivalent to the least-area `Δ`, so it is least area. Hence the kept cell and `m₁` are unchanged by removing
   `x ∪ y`.
4. **x ≠ y.** `a ≠ b` in a pairwise-compatible family, so the face sets are disjoint, and each is nonempty
   (`faces_nonempty`).
5. **Proper source arc.** The gap arc misses the nonempty source arc of `x`, so its length is less than `|∂Π|`,
   as `SectionPocketFaceSetFirstTurnInput` requires.
6. **Edge conditions for the inner sides: settled by the landed copy.** The walk must have distinct darts and use
   no edge in both directions (`FirstTurnWalk.isNoncrossingClosedWalk`). The proved `SectionPocketRegionsCopyStatement`
   (`Estimating/OsinPocketFaceSetOnCopy`) gives a copy with no `IsOuterSideDart` and no `IsCellSideDart`. Both are
   stated for `a.2.rightSide ++ a.2.leftSide`, so they cover the inner sides as well as the outer ones: no exterior
   face across a side, and no relator cell of perimeter > 1 across a side. The copy also has no edge joining two
   distinct regions. The inclusive `CopyClean` used only the outer halves.

## Formal target

This route bypasses `p10LS_SelectionArcStatement` and `p10LS_SelectionStatement`; it does not prove them. It
proves `OsinSectionPocketFaceSetFirstTurnSectionStatement` (`Estimating/OsinPocketPinchFirstTurnAssembly`). Then
`osinSectionPocketCutSection_of_residualsFirstTurnSection` with the proved binder 7
(`pocketPinchLabelledFirstTurnSection`) and the collar gives `OsinSectionPocketCutSectionStatement`. The wiring
into the torsion-free endpoints is done by ms-nm-uncond-b and nm-gl03d. The turn lemmas are
`Estimating/OsinPocketExclusiveTurns.lean` (lane nm-switch-core).
