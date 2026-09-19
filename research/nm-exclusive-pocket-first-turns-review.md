---
rg: 2
id: nm-exclusive-pocket-first-turns-review
kind: claim
title: Referee review of the exclusive-pocket route for Osin 9.7(b) — the source claims check at Osin v3; the route is sound on paper given nonempty source and target arcs of the two extreme regions, R-cell-free regions and at least two of them; it bypasses p10LS_SelectionArcStatement rather than proving it, and its Lean target is a first-turn PocketFaceSet producer feeding the proved first-turn pinch
distinct_from:
  nm-exclusive-pocket-first-turns: that is the route under review; this checks its source claims at Osin v3, its turn-by-turn argument, its open items, and its fit with the Lean interfaces.
---

**ESTABLISHED (referee bh-ref-t0, 2026-09-19; review of nm-switch-core's notes 6ba8cac61a, ce74d6fd09).**
Non-MF-critical. This is a review of a paper route, not of Lean code; no build was run.

Sources read:
- Osin arXiv:math/0411039v3, pp. 8, 13, 14, 29–30, 34–35, 37.
- On origin/main: `P10LocalSelect/ArcStatement.lean` and `Statement.lean`,
  `NMUncondB/TorsionFreeSelection.lean`, `Estimating/OsinPocketPieces.lean` (`PocketFaceSet`),
  `OsinPocketPinchFirstTurn.lean` (`FirstTurns`), `OsinPocketFirstTurnWalk.lean` (`FirstTurn`),
  `OsinPocketGoodCornersSection.lean`, `ContiguityGeometry.lean`, `RegionCandidate.lean`, `Embedded.lean`
  (`CyclicArc`, `Contiguity`).

## Verdicts

| item | verdict |
|---|---|
| (1) Osin asserts `Γ¹` without argument; 0-refinement convention; Olshanskii credit | **PASS** (one quotation tightened) |
| (2a) Osin's argument survives excluding `x`, `y` | **PASS** on paper |
| (2b) first-turn order along sides and arcs, and (R1) automatic | **PASS** |
| (2c) junction turns need (R2) | **PASS given (R2)**; (R2) is **OPEN** formally, for the target arcs even on paper |
| (2d) `F⁻` is a valid `PocketFaceSet` | **PASS modulo two unstated hypotheses**: the regions are R-cell-free, and `x ≠ y` |
| (3) fit with `p10LS_SelectionArcStatement` | **does not match; the route bypasses it**. The right Lean target is named below. |

## (1) The source

- **p. 35, proof of 9.7(b).** The quoted text is verbatim: "Let us consider the subdiagram Γ¹ of Δ such that:
  (i) ∂Γ¹ = s₁t₁s₂t₂ … (ii) Γ¹ contains all Γ_{i,1}'s." No construction or existence argument follows. Osin next
  defines `m₁` as the number of R-cells in `Γ¹` and uses it at once.
- **p. 8.** The 0-refinement convention "enables us to assume that all diagrams a[re] homeomorphic to a disc",
  citing [21] = Olshanskii, *Geometry of defining relations in groups* (Kluwer 1991), Ch. 4.
- **p. 14.** "The proof of this lemma is actually given in [23, Lemma 6.6] (see also the addendum in [24])".
  - [23] = Olshanskii, IJAC 3 (1993), no. 4, 365–409.
  - [24] = Olshanskii, J. Algebra 226 (2000), no. 2, 807–817.
- **p. 29.** The note's quotation should read: "Lemma 4.4 (as well as Lemma 9.7) is, in fact, proved in [23],
  although it is stated in a slightly different way there … all results of this section should be credited to
  Olshanskii."
- **Not checked here.** The DGO §3 statement.
- **Relevant for (2).** Osin's p. 13 definition says an ε-contiguity subdiagram is bounded by a *simple* closed
  path `s₁q₁s₂q₂` with `l(sᵢ) ≤ ε`, and *contains no R-cells*.

## (2) Soundness of the repair

**(2a) Osin's argument survives.**
- *Sides.* The inner sides are side arcs of `Γ_{i,1}`'s, so their lengths are `≤ ε`, which is all the `k₁, k₃` bounds
  in (40) use.
- *Arcs.* The gap arc lies in `∂Π` and the target arc in `q₁`, so `k₂ ≤ 1` and the final `t₂`-sum are unchanged.
- *`m₁`.* The excluded regions contain no R-cells, by the p. 13 definition, so `m₁` and `m(Π)` are unchanged, and
  "`Π′` counts in `m(Π)`" still holds.
- *`m₁ = 0`.* `x ∪ Γ¹⁻ ∪ y` is R-cell-free with sides `≤ ε`, so it is one ε-contiguity subdiagram, contradicting
  `𝓜` as Osin argues.
- *One unstated case.* If only one `Γ_{i,1}` exists, then `x = y`, `F⁻` is empty, and `m₁ = 0` trivially. The
  route needs `x ≠ y`.

**(2b) First-turn order along the sides and arcs.**
- *The definition.* `PocketFaceSet.FirstTurns` asks, for consecutive cycle darts `d, e`, for
  `FirstTurn (cycle.reverse.map α) (α e) (α d)`. That is: rotating from `e` reaches `α d` past darts off the cycle
  edges.
- *Along an inner side.* This is literally the region's own `BoundaryStep`. Its intermediate darts lie on
  region-internal edges, both of whose faces are region faces. Such an edge has no `F⁻` face, so it is never a
  cycle edge. (R1) is therefore automatic, as the second note says, and needs no disc hypothesis.
- *Along the gap arc and the target arc.* Consecutive darts are one σ-step apart (the corner of `Π` or of the
  outer face), so `k = 1`, with no intermediate darts.

**(2c) The junctions.**
- *With (R2).* At a side → arc junction the rotation from the arc dart passes the corner of `Π` (or of the outer
  face), then one edge of the region's source arc (or target arc), which is not a cycle edge, then the region's own
  boundary step into its side. All intermediate darts are off the cycle. The degenerate junctions (an empty gap arc
  or target arc of `F⁻`) run through both regions' arc edges the same way, again using (R2) for both regions.
- *Without (R2).* If an arc of `x` is empty, the sweep passes into material outside `F` at that vertex. There
  `F⁻` may touch the same vertex in another corner, and first-turn order can fail.
- *(R2) is not automatic formally.* `CyclicArc` allows `length = 0`, and `RegionCandidate.weight` counts
  `sourceArc.length + targetArc.length`. So a distinguished family only forces each region's **total** weight to
  be positive.
- *Source arcs can be arranged.* On paper, a region with an empty source arc contributes nothing to
  `Σ(Π, Γ_{i,1}, q₁)`. Take `x, y` extreme among the regions with nonempty source arcs; the others stay in `F⁻` and
  are R-cell-free.
- *Target arcs remain OPEN.* No argument for them was found, on paper or formally. This is the route's genuine open
  item. Either prove it for exterior regions, or extend the junction analysis to an empty target arc.

**(2d) Validity of `F⁻` as a `PocketFaceSet`, field by field.**
- *`outerFace_not_mem`, `source_not_mem`.* Immediate: `Π` and the outer face are not in `F`.
- *`kept_mem`.* This needs a relator cell in `F ∖ (x ∪ y)`, which holds when `m₁ > 0` **and** `x, y` contain no relator cell.
  - `ContiguityGeometry` and `RegionCandidate` do **not** record R-cell-freeness: there is no such field, and none
    was found by grep.
  - So this is an **unstated formal hypothesis**. It must be supplied from the exterior-region producer or proved.
- *`decomposition`.* `∂F⁻` is obtained from `∂F` by deleting the outer side, source arc and target arc of each of
  `x` and `y`, and inserting their inner sides. That is correct because `x, y` are extreme and disjoint, so their
  arcs sit at the ends of `t₁, t₂`. The formal statement must also handle `CyclicArc` base positions, including
  wrap-around.
- *Side bounds.* These come from the regions' `rightSide/leftSide` length and norm fields.
- *`lo_le`, `le_hi`.* These hold because the new target arc is a sub-arc of the old one.

## (3) Fit with the Lean statements

- **The route does not prove `p10LS_SelectionArcStatement`.**
  - That statement quantifies over all planar maps and cycles `c` satisfying `¬p10FM_FirstTurns` and
    `p10FM_AllCrossed`, and asks for a good lobe. It is the formal shadow of the inclusive pocket.
  - The route instead ensures that the pocket actually used is in first-turn order, so the rose branch is never
    entered. `p10LS_SelectionArcStatement` itself stays **OPEN** and untouched.
  - It also does not follow that the exclusive cycle falsifies the hypothesis `¬p10FM_FirstTurns`, since that
    predicate differs from `PocketFaceSet.FirstTurns`. The route never needs that.
- **The right Lean target** is a producer of the following shape. Given the distinguished exterior family at `Π`
  and `q₁`, with at least two exterior regions, R-cell-free regions, `m₁ > 0` and (R2), it builds
  `K : PocketFaceSet D eps X lo hi` on `F ∖ (x ∪ y)` together with `K.FirstTurns`.
  - Its consumer is already proved: `pocketPinchFirstTurns` and `pocketPinchLabelledFirstTurnSection` (binder 7,
    in `OsinPocketGoodCornersSection`).
- **Rewiring.** The non-MF chain currently takes `hsel : p10LS_SelectionStatement` in
  `NMUncondB/TorsionFreeSelection.lean`, through `p10LS_quadrantMove_of_selection` and
  `GL03DQuadrant.relativeGreendlinger_zero_of_allCells_of_quadrantMove`. The producer would replace that input at
  the call that now builds the inclusive pocket from `PocketWalk.exists_of_exteriorAt`. Osin's `m`-minimality
  must then be read with exclusive pockets, which is harmless given R-cell-free regions.
- **Not traced here.** The exact consumer signature on the Greendlinger side.

## Lesson

- **The rose case is a modeling artifact.** The formal rose case comes from building the pocket along the regions'
  outer sides, which face uncontrolled material.
- **Why the repair works.** Building the pocket along their inner sides makes every turn a region boundary step,
  so first-turn order is free.
- **What is left.** Only the two junctions at each region, which need its arcs to be nonempty, and the
  R-cell-freeness of the excluded regions, which Osin's definition gives on paper but the formal candidates do
  not record.
