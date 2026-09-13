# hull-count94

## Scope
Roster target: `OsinLemma94RunInput` and its counting reduction, closed, at the Prop hull-unbound's
assembly consumes. That Prop is `OsinLemma94SectionStatement` (`Estimating/OsinAppendixSections.lean`),
passed as `h94` to `OsinAppendixAssembly.osinLemma97Section_of_inputs`.

## On main
- `Estimating/OsinLemma94RunInput.lean` and `Estimating/OsinLemma94Counting.lean` (82ba54dfb,
  unmodified). PROBE GREEN 0913-010901-92003 at base e8702f1b1, both COMPILED. Axioms are within
  {propext, Classical.choice, Quot.sound}.
- `osinLemma94Section_of_runInput : OsinLemma94RunInput → OsinLemma94SectionStatement` is proved
  from the closed `unboundComponentWordPolygonsMonotone` and `isHyperbolicSpace_cayley_of_fourPoint`.

## Residual Prop
`OsinLemma94RunInput`: under the Lemma 9.4 hypotheses, every globally distinguished section family
`S` gives `Nonempty (OsinLemma94ComponentPolygons D lambda c eps S)`. Its fields are `arc_budget`,
`side_le`, `closed`, `step`, `quasiGeodesic`, `short`, `covers` and `no_connector`.

## Finding: `no_connector` has an orientation gap
- `no_connector : ∀ k, WordConnectorPair .. → False` forbids unoriented pairs. `WordConnectorPair`
  fixes `a < a'` but allows `b, b'` in either order ("The second side can be read in either
  direction"). The orientation is lost in two places:
  - `threeClassPolygon` returns `SidePair` ("Orientation on either side is immaterial"); in the base
    case, `exists_long_close_pair` ends with `β ≤ |s' - s|`.
  - `exists_originalArcPair_of_class_near` chooses Morse indices existentially.
- The planar Case 1 contradiction is `RealizedSectionFamily.false_of_quadrilateral_region`. It needs
  the face walk `X ++ targetBoundaryDarts .. ++ Y ++ sourceArc.reverseDarts` with `s1 = X` and
  `s2 = Y`. So the connectors join end(P) to start(T) and end(T) to start(P). With polygon sides
  read in face-walk order, this is the antiparallel case `b' < b`.
- A parallel pair (`b < b'`) in a disc face needs two crossing chords, so no such subdiagram exists:
  a positively oriented subdiagram reads both arcs in the direction of the walk. `no_connector` as
  drafted therefore excludes pairs that no surgery contradicts. It is not refuted, but Osin's route
  gives no proof of it.
- Osin's printed Lemma 3.7 bounds `max{dist((q1)−,(q2)−), dist((q1)+,(q2)+)}` without fixing the
  orientation of the subsegments, so it is the unoriented statement. His Case 1 boundary
  `q1 s1 q2⁻¹ s2` silently uses the antiparallel one.

## Proposed correction
1. Build an oriented metric layer in new modules, with no edits to existing metric modules.
   - Oriented Lemma 25 for small polygons: take first-visit witnesses (lexicographic minimum over
     side index and parameter, at the chord threshold). They are monotone along the chord, by the
     chord lemma applied to the prefix broken line plus one connector. The existing pigeonhole then
     gives `s < s'` together with `r < r'`, which is the antiparallel case.
   - `OrientedSidePair` and `OrientedClassPair`. The restriction, rotation and inner-cut transports
     only translate parameters, so they keep orientation. The bisection recursion keeps chords out
     of the classes.
   - The oriented three-class polygon lemma.
   - A monotone Morse index choice: on a (λ,c)-quasi-geodesic word, indices near geodesic parameters
     `t < t'` with `t' - t` above a constant satisfy `k < k'`. The proof uses the Morse lemma on the
     prefix subword and thin triangles.
   - `WordConnectorPair` with `target_backward : b' < b`, and the component-family theorem at that
     orientation.
2. Restate `OsinLemma94RunInput` and `OsinLemma94Counting` on the oriented connector. Neither has
   users outside these two files on origin/main.

## Next
- The oriented Lemma 25 module first, in new files, unless the lead reassigns the metric layer.
- Producer:
  - Reduce with `exists_unselectedGFacesReduced`, which keeps the card and the unbound sum.
  - Take polygons from the closed loops of each unselected G-face walk.
  - Case 1 goes through `false_of_quadrilateral_region`; Case 2 through the cutting paths.

## Coordination
- hull-unbound integrates h94 and owns `Estimating/UnboundWordPolygonMonotone.lean`.
- The other metric modules are in no lane's file list: `Olshanskii*`, `Estimating/UnboundPolygonGeometry`,
  `UnboundWordPolygon`, `UnboundComponentWordPolygons` and `UnboundWordConnectors`.
