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
`OsinLemma94DartMinimal`, `OsinLemma94CaseOneWalk` and `OsinLemma94ChainRespell`.
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
  - `OsinLemma94PolygonRealizationInput` (hull-unbound): `∃ P : OsinLemma94RealizedPolygons S,
    P.Maximal`.
  - `OsinLemma94PolygonCountInput` (hull-count94): `∃ K, ∃ eps0, ∀ eps ≥ eps0, ∃ L, ∃ rho0, ...`,
    `∀ P, P.Maximal → P.SideBudget K ∧ P.Covers L`. `K` is chosen before `ε` and `L` after.
  - `OsinLemma94CaseOneInput` (theoremc-retire): `∀ P, P.Maximal → ∀ k (C : WordConnectorPair ..),
    C.b' < C.b → P.kind k C.target ≠ .cutting → False`. The pair is over `symmetricLabelAlphabet D`.
  - `OsinLemma94CaseTwoInput` (sec5-sentences): the same with `P.kind k C.target = .cutting`.
- The slack `L n` in `Covers` costs a factor `2` in `√ρ`. For `ρ ≥ 4 L²` and `ρ ≥ 4 ρ_metric`, the
  metric half is applied at `⌊ρ / 4⌋` (`dense_of_covers`, `unbound_lt_of_pieces`).

## Respelling surgery (landed)
`Estimating/OsinLemma94ChainRespell.lean` (7a225d1d0, green in probe 0913-090448-70090). All names
are in `GloballyDistinguishedSectionFamily`.
- Definitions: `UnselectedGFace`, `RunsBackAcross` (the `cutting_interior` form) and
  `DegreeTwoJoints`.
- `CornerInsertionInput` (simple-group): insert a legal word across an unselected `G`-face, from the
  corner before a chain to the corner after it. The result has `2 |word|` more darts and the same
  unbound sum, and the chain runs between two distinct unselected `G`-faces.
- `PendantPathRemovalInput` (jacobson): remove a path that starts at a leaf inside an unselected
  `G`-face. The result has `2 |path|` fewer darts and the same unbound sum.
- `SeparatingPathRemovalInput` (hull-unbound): `Surgery.GFaceMerge` on the first edge, then
  `PendantPathRemovalInput` on the rest.
- `ChainRespellInput`: a strictly shorter nonempty legal word with the value of the chain gives
  fewer darts and the same unbound sum. `chainRespellInput_of_pieces` derives it from the insertion
  and the separating removal.

## Findings
- Connector orientation: `WordConnectorPair` fixes `a < a'` and leaves `b`, `b'` in either order.
  Cases 1 and 2 draw both connectors as chords of one face, and the chords are disjoint exactly when
  `b' < b`. So only backwards pairs are refutable, and the metric half is stated for them.
- One constant `K` replaces `53` and `4`, since Steiner corners may push `k_i` above `4 n_i`.
- Labels: `label_admissible` of a distinguished family is `LabelLegal (symmetricLabelAlphabet D)`,
  so cutting and short sides need not be `IsAdmissible D`. So the sides are measured over the
  symmetric alphabet, which has the same Cayley graph. theoremc-retire's
  `OsinLemma94CaseOneWalkStatement` still uses `WordConnectorPair D`. It compiles, but it must be
  restated over `symmetricLabelAlphabet D` before it can feed `OsinLemma94CaseOneInput`.
- The constant `c + 2`: suppose a subpath of length `L` of a cutting path violates `(λ, c + 2)`.
  - If its endpoints differ, a geodesic word of length at most `L − 3` respells it.
  - Otherwise `L ≥ 3`, and the subpath without its last letter is respelled by one letter.
  In both cases `ChainRespellInput` against `DartMinimal` refutes it.
- LoopCut gate: none of the three producers of competitor regions excludes `target = some source`.
  - Case 1 with both connector sides on arcs of one cell forces a loop competitor.
  - So does SharedEdge on an edge with one cell on both sides.

## Risks
- Budget: `K` independent of `ε` needs the number of unselected `G`-faces and their sides bounded by
  an Euler count in `n` alone.
- Case 1 on one cell needs a loop competitor (LoopCut gate above).
- Separating removal needs dart identification through `Surgery.GFaceMerge.keep` (in progress).

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

## Residual Props of `osinLemma94Section_of_planarPieces`
- `OsinLemma94PolygonRealizationInput` (hull-unbound). It needs `ChainRespellInput`, hence
  `CornerInsertionInput` (simple-group) and `PendantPathRemovalInput` (jacobson).
- `OsinLemma94PolygonCountInput` (hull-count94).
- `OsinLemma94CaseOneInput` (theoremc-retire).
- `OsinLemma94CaseTwoInput` (sec5-sentences).

## Next
- Prove `SeparatingPathRemovalInput` from `PendantPathRemovalInput`.
- Build `Estimating/OsinLemma94PolygonRealization.lean` over `ChainRespellInput`, with
  ghw-assembly.
- Then `osinLemma94Section_closed` with `#audit_closed_axioms`, once the other pieces close.
- Then help hull-respell with hgreendlinger.
