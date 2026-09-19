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
"Lemma 9.7 is, in fact, proved in [23]… all results of this section should be credited to Olshanskii"
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

## To check before building

1. (R1) is automatic, checked 2026-09-19. `ContiguityGeometry.boundary` is a `FaceSetBoundary` whose `BoundaryStep`
   is `facePerm` followed by internal moves. With `facePerm = sigma ∘ alpha`, a step `d_r → e_r` gives
   `e_r = sigma^k (alpha d_r)` past darts on region-internal edges, which is exactly `FirstTurn` for the
   reversed dart pair of the pocket. The inner sides are y.rightSide and x.leftSide (the producer's outer sides
   are y.leftSide and x.rightSide).
2. Do they satisfy (R2)? Check `CyclicArc` lengths on exterior regions.
3. Is F \ (x ∪ y) a valid `PocketFaceSet` with the kept cell (a relator cell, hence in neither region), and are
   the side bounds kept?
4. What does the J. Algebra 2000 addendum change in Olshanskii's Lemma 6.6?
