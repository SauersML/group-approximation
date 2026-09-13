# hull-unbound lane report

## Scope
Integrator of h94: the closed `theorem osinLemma94Section_closed : OsinLemma94SectionStatement`
(Osin, arXiv:math/0411039v3, §9, Lemma 9.4, in `Estimating/OsinAppendixSections.lean`). Roster W1:
this lane keeps realization and the assembly. The count piece (side budget and covers) goes to
hull-count94, Case 1 to theoremc-retire and Case 2 to sec5-sentences.

## First split (landed)
`Estimating/OsinLemma94Pieces.lean` (b8441172e, compiled in probe 0913-042440-98733):
`osinLemma94Section_of_pieces (hmetric) (hrun) : OsinLemma94SectionStatement`.
- The metric half `OsinLemma94AntiparallelMetricStatement` is closed by sec5-sentences:
  `osinLemma94AntiparallelMetric` in `Estimating/OsinLemma94AntiparallelMetric.lean` (e3da1ba60).
- `OsinLemma94PlanarRunInput` is superseded by the second split below.

## Second split (landed)
`Estimating/OsinLemma94PlanarPieces.lean`: 80790fad1, then f2cc2be97. The revision measures over
`symmetricLabelAlphabet D` at `c + 2`. It is green in probe 0913-090448-70090, together with
`OsinLemma94DartMinimal`, `OsinLemma94CaseOneWalk` and `OsinLemma94ChainRespell`. hull-count94
moved `K` after `ε` in the metric and count Props (9f8779c4e).
```lean
theorem osinLemma94Section_of_planarPieces
    (hmetric : OsinLemma94AntiparallelMetricStatement.{u, w})
    (hreal : OsinLemma94PolygonRealizationInput.{u, w, v})
    (hcount : OsinLemma94PolygonCountInput.{u, w, v})
    (hone : OsinLemma94CaseOneInput.{u, w, v})
    (htwo : OsinLemma94CaseTwoInput.{u, w, v}) :
    OsinLemma94SectionStatement.{u, w, v}
```
- `OsinLemma94RealizedPolygons S`: the unselected `G`-faces of `S.diagram`. Each face walk is cut
  into sides of kind `cell j` (A1), `boundary j` (A2), `cutting` or `short` (A3). The side words
  are dart labels. The model test is `ofNoFaces` with `ofNoFaces_maximal`.
- The sides are measured over `symmetricLabelAlphabet D`:
  - (A1) arcs, (A2) arcs and cutting paths are `(λ, c + 2)`-quasi-geodesic;
  - (A3) sides are legal, of length at most `ε`.
- The assembly applies the metric half at `(symmetricLabelAlphabet D, c + 2)`, with hyperbolicity
  through `symmetricLabelAlphabet.carrier_eq`.
- `GloballyDistinguishedSectionFamily.DartMinimal`: the fewest darts among optimal families with the
  same unbound sum. It is the Case 2 measure, in place of `∑ l(t_i)`. `exists_dartMinimal` keeps the
  family card, since two optimal families have equal weight and card (`family_card_eq`).
- Every piece Prop has the prefix of `OsinLemma94SectionStatement` up to
  `S.family.card ≤ 3 * (...)`, followed by `S.DartMinimal →`.
  - `OsinLemma94PolygonRealizationInput` (hull-unbound, CLOSED at 4002b9371):
    `∃ P : OsinLemma94RealizedPolygons S, P.Maximal`.
  - `OsinLemma94PolygonCountInput` (hull-count94): `P.SideBudget K ∧ P.Covers L` for maximal `P`.
  - `OsinLemma94CaseOneInput` (theoremc-retire): `∀ P, P.Maximal → ∀ k (C : WordConnectorPair ..),
    C.b' < C.b → P.kind k C.target ≠ .cutting → False`. The pair is over `symmetricLabelAlphabet D`.
  - `OsinLemma94CaseTwoInput` (sec5-sentences, CLOSED at e0e94015d): the same with
    `P.kind k C.target = .cutting`.
- The slack `L n` in `Covers` costs a factor `2` in `√ρ`. For `ρ ≥ 4 L²` and `ρ ≥ 4 ρ_metric`, the
  metric half is applied at `⌊ρ / 4⌋` (`dense_of_covers`, `unbound_lt_of_pieces`).

## Respelling surgery (landed)
`Estimating/OsinLemma94ChainRespell.lean` (7a225d1d0, green in probe 0913-090448-70090). All names
are in `GloballyDistinguishedSectionFamily`.
- Definitions: `UnselectedGFace`, `RunsBackAcross` (the `cutting_interior` form) and
  `DegreeTwoJoints`.
- `CornerInsertionInput`: PROVED by simple-group, `cornerInsertionInput` in
  `Estimating/OsinLemma94CornerInsertion.lean` (f7538e223, green in probe 0913-123745-5546).
- `PendantPathRemovalInput`: PROVED by jacobson, `pendantPathRemovalInput` in
  `Estimating/OsinLemma94PendantRemoval.lean` (61c2ade8e, green in probe 0913-102123-19053).
- `SeparatingPathRemovalInput`: PROVED by `separatingPathRemovalInput_of_pendant` in
  `Estimating/OsinLemma94SeparatingRemoval.lean` (7d4a2515f, green in probe 0913-093115-86638).
  A `Surgery.GFaceMerge` on the first edge leaves the rest as a pendant path in the merged face
  (`GFaceMerge.facePerm_keep_of_ne`, `GFaceMerge.sigma_keep_eq_self`).
- `ChainRespellInput`: a strictly shorter nonempty legal word with the value of the chain gives
  fewer darts and the same unbound sum. `chainRespellInput_of_pieces` derives it from the insertion
  and the separating removal, so both of its inputs are closed.

## Realization split (landed)
`Estimating/OsinLemma94PolygonRealization.lean` (1130c8dbc, green in probe 0913-095511-56070).
`osinLemma94PolygonRealizationInput_of_pieces (hcutting) (hcells) (hboundary) (hpartition) :
OsinLemma94PolygonRealizationInput`, with `ε₀ = ρ₀ = 1`.
- `gFacesApart_of_dartMinimal` (proved): two different unselected `G`-faces share no edge, since a
  `G`-face merge removes two darts and keeps the unbound sum.
- `OsinLemma94CuttingChainsInput`: DERIVED by `osinLemma94CuttingChainsInput_of_pieces` in
  `Estimating/OsinLemma94CuttingChains.lean` (108236c25, green in probe 0913-111910-27621), from
  `ChainRespellInput`, `PendantPathRemovalInput` and `QuasiGeodesicRespellInput`.
  - A leaf inside an unselected `G`-face contradicts `DartMinimal` (`not_leaf_of_dartMinimal`).
  - So a cutting chain never holds a dart together with its reverse
    (`alpha_not_mem_of_dartMinimal`).
  - A violating subchain is rotated to the front of the face walk and respelled.
- `QuasiGeodesicRespellInput`: PROVED by `quasiGeodesicRespellInput` in
  `Estimating/OsinLemma94QuasiGeodesicRespell.lean` (bbb8585ab, green in probe 0913-120651-61632).
  hull-component's `exists_shorter_respelling_of_not_isLambdaCQuasiGeodesicWord`
  (`Estimating/OsinLemma94WordRespelling.lean`, 6b5a1f7d1) proves the same binders. The names
  differ, so both modules can be wired, and the lead keeps both.
- `OsinLemma94CellArcsInput`: PROVED by ko-closed, `osinLemma94CellArcsInput_holds` in
  `Estimating/OsinLemma94CellArcs.lean` (5e5a98049, green in probe 0913-104724-79090).
- `OsinLemma94BoundaryArcsInput`: PROVED by cite-hull, `osinLemma94BoundaryArcsInput` in
  `Estimating/OsinLemma94BoundaryArcs.lean` (1b453429f, green in probe 0913-111012-12718).
- `OsinLemma94PolygonPartitionInput`: PROVED by ghw-assembly, `osinLemma94PolygonPartitionInput`
  in `Estimating/OsinLemma94PolygonPartition.lean` (746028b24, green in probe 0913-132334-2532).
  The unselected `G`-faces with walks cut by `sidesOf` form `S.realizedPolygons`, and
  `realizedPolygons_maximal` proves them maximal. The chain is `OsinLemma94PolygonLists`
  (269a91ab3), `PolygonKinds` (5c69ca42d), `PolygonSides` (a76186267) and `PolygonMaximal`
  (9f03bfcd3).
- So `osinLemma94PolygonRealizationInput : OsinLemma94PolygonRealizationInput` is closed, under
  `#audit_closed_axioms` in `Estimating/OsinLemma94SectionResiduals.lean`.

## Assembly over the open pieces (landed)
`Estimating/OsinLemma94SectionResiduals.lean` (4da8d3ef8, 0087a5095, 409bbbf72, then 4002b9371,
green in probe 0913-133025-35313; queued for wiring):
```lean
theorem osinLemma94PolygonRealizationInput : OsinLemma94PolygonRealizationInput.{u, w, v}

theorem osinLemma94Section_of_residuals
    (hcount : OsinLemma94PolygonCountInput.{u, w, v})
    (hone : OsinLemma94CaseOneInput.{u, w, v}) :
    OsinLemma94SectionStatement.{u, w, v}
```
The realization theorem passes `cornerInsertionInput`, `pendantPathRemovalInput`,
`separatingPathRemovalInput_of_pendant`, `quasiGeodesicRespellInput`,
`osinLemma94CellArcsInput_holds`, `osinLemma94BoundaryArcsInput` and
`osinLemma94PolygonPartitionInput` through `osinLemma94PolygonRealizationInput_of_partition`. The
assembly adds `osinLemma94AntiparallelMetric` and `osinLemma94CaseTwoInput`, then applies
`osinLemma94Section_of_planarPieces`.

## Findings
- Connector orientation: `WordConnectorPair` fixes `a < a'` and leaves `b`, `b'` in either order.
  Cases 1 and 2 draw both connectors as chords of one face, and the chords are disjoint exactly when
  `b' < b`. So only backwards pairs are refutable, and the metric half is stated for them.
- One constant `K` replaces `53` and `4`, since Steiner corners may push `k_i` above `4 n_i`.
- Labels: `label_admissible` of a distinguished family is `LabelLegal (symmetricLabelAlphabet D)`,
  so cutting and short sides need not be `IsAdmissible D`. So the sides are measured over the
  symmetric alphabet, which has the same Cayley graph.
- The constant `c + 2`: suppose a subpath of length `L` of a cutting path violates `(λ, c + 2)`.
  - If its endpoints differ, a geodesic word of length at most `L − 3` respells it.
  - Otherwise `L ≥ 3`, and the subpath without its last letter is respelled by one letter.
  In both cases `ChainRespellInput` against `DartMinimal` refutes it.
- Empty arcs: `(λ, c + 2)` on the empty word needs `c ≥ −2`, so the arc pieces take `0 ≤ c`.
- `Maximal` never checks the wrap pair (last side, side 0). With one section, the forced cut at
  outer position 0 must be the base of its face.
- LoopCut gate: none of the three producers of competitor regions excludes `target = some source`.
  - Case 1 with both connector sides on arcs of one cell forces a loop competitor.
  - So does SharedEdge on an edge with one cell on both sides.
  Ruling (A) adds `target ≠ some source` to `RespectsSections`. ghw-charp2's census marks
  `false_of_quadrilateral_region` (`Estimating/OsinUnboundCaseOne.lean`) and
  `false_of_digon_toward_cell` at `i₂ = i` (`Estimating/OsinUnboundSharedEdge.lean`) as same-cell
  forceable.

## Risks
- Budget: `K` independent of `ε` needs the number of unselected `G`-faces and their sides bounded by
  an Euler count in `n` alone (hull-count94, `OsinLemma94PolygonSideBudgetInput`).
- The Case 1 one-cell connector pair (below).

## One-cell connector pair (option (2), gated)
Ruling (lead, 09-13): option (2). The metric Prop delivers the one-cell pairs at `λ⁻¹(ε + c)`,
and ko-closed proves case (a) by the value argument. The gate is that the metric owners confirm
F1's quantifier order. The fallback, option (1), counts one-cell pairs separately and needs a new
ruling with hull-count94. `OsinLemma94CaseOneSameCellStatement` has no `OsinLemma97Below` binder,
so as spelled it is as hard as Lemma 9.7 on smaller diagrams, and no lane proves that spelling.
- The metric Prop `OsinLemma94AntiparallelMetricStatement` (Pieces:97) and its conclusion
  `OsinLemma94DensePolygonsAntiparallel` (Pieces:71) are in this lane's
  `Estimating/OsinLemma94Pieces.lean`. After F1 the order is `∃ ε₀, ∀ ε ≥ ε₀, ∀ K, ∃ ρ₀ > 0,
  ∀ ρ ≥ ρ₀`. So `λ`, `c` and `ε` are fixed before `K` and `ρ₀`, and a conjunct at length
  `λ⁻¹(ε + c)` needs no reordering. Users: `OsinLemma94AntiparallelMetric` (sec5-sentences) and
  `OsinLemma94PlanarPieces`.
- `osinLemma94Section_closed` is built over the option (2) spelling once it lands.

Rule 22 users of a PlanarPieces statement patch, on origin at 1b6c528fa:
- `OsinLemma94CaseOneInput` (PlanarPieces:395): `OsinUnboundCaseOneFace`,
  `OsinUnboundCaseOneRun`, `OsinLemma94CaseOneWalk` and `OsinLemma94SectionResiduals`.
  `OsinCConditionLineModel` names it only in its docstring.
- `osinLemma94Section_of_planarPieces`: only `OsinLemma94SectionResiduals`.
- Other direct importers of PlanarPieces: `OsinLemma94DartMinimal`, `OsinLemma94ChainRespell`,
  `OsinLemma94InsertionTransport`, `OsinLemma94PolygonCovers` and `DiscEmbeddingAwayUnbound`.
- Co-probe list: `OsinLemma94SectionResiduals`, `OsinUnboundCaseOneRun`,
  `OsinLemma94CaseOneWalkHolds`, `OsinLemma94DartMinimal`, `OsinLemma94PolygonCount` (it reaches
  `PolygonCovers`) and `DiscEmbeddingAwayUnbound`.

## On main (surgery layer)
- `Estimating/SingletonFaceRegion.lean` (bd53291cd): `ContiguityGeometry.ofSingletonFace`,
  `RegionCandidate.familyWeight_lt_cons_singleton`, `cons_singleton_pairwise`.
- `GFaceQuadrilateralRegion.lean` (64e1a784f), `Estimating/OsinUnboundCaseOne.lean` (ccde452ae):
  `RealizedSectionFamily.false_of_quadrilateral_region`,
  `RegionCandidate.respectsSections_of_sameTargetProfile`.
- `SurgeryFaceEdgeDoubling.lean` (ceb7135c3) and `SurgeryFaceEdgeDoublingRegions.lean` (b67574c33).
- `Estimating/OsinUnboundSharedEdge.lean` (8009a06ff, green in probe 0913-042440-98733, wired in
  wave 5): `false_of_unbound_shared_edge`. An unbound dart on an edge shared with a relator cell or
  the exterior contradicts maximality.

## Residual Props of `osinLemma94Section_of_residuals`
- `OsinLemma94PolygonCountInput` (hull-count94 with sec5-sentences).
  `osinLemma94PolygonCountInput_of_sideBudget` reduces it to `OsinLemma94PolygonSideBudgetInput`.
- `OsinLemma94CaseOneInput` (theoremc-retire). On main `osinLemma94CaseOneInput_of_walk
  osinLemma94CaseOneWalk` proves it, but no declaration composes them. Patch 10(f) is overruled,
  so `_of_walk` stays, but once ghw-charp2's co-probe lands ruling (A) it takes an
  `OsinLemma94CaseOneSameCellStatement` binder, and a closure composed on today's main would
  become conditional. The one-cell pairs go by option (2) below.

Closed pieces plugged in:
- `OsinLemma94CaseTwoInput`: sec5-sentences, `osinLemma94CaseTwoInput` in
  `Estimating/OsinLemma94CaseTwo.lean` (e0e94015d, green in probe 0913-131149-5355).
- `OsinLemma94PolygonPartitionInput`: ghw-assembly, `osinLemma94PolygonPartitionInput` in
  `Estimating/OsinLemma94PolygonPartition.lean` (746028b24, green in probe 0913-132334-2532), over
  `OsinLemma94PolygonLists`, `PolygonKinds`, `PolygonSides` and `PolygonMaximal`.

## Next
- Land the option (2) respelling of `OsinLemma94DensePolygonsAntiparallel` in
  `OsinLemma94Pieces.lean`, co-probed with `OsinLemma94AntiparallelMetric`, PlanarPieces and
  `OsinLemma94SectionResiduals`, once the lead names who drafts it (asked 09-13).
- Then `osinLemma94Section_closed` with `#audit_closed_axioms`, over the option (2) spelling, once
  the count and Case 1 are proved and ghw-charp2's co-probe of ruling (A) has landed.
- Pocket pinch help (approved): ghw-assembly has the wrap case with dgo-geometric and hull-respell.
  This lane asked hull-respell and ghw-assembly once each for a piece. If neither names one, the
  lead gives an item.
