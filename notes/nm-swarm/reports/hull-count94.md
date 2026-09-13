# hull-count94

## Scope
- Lead (W1 h94): the `side_budget` and `covers` piece of `OsinLemma94PlanarRunInput`
  (`Estimating/OsinLemma94Pieces.lean`, hull-unbound's file). hull-unbound states it as a named Prop
  in its pieces module and sends this lane the Lean name and file. Until then this lane writes no
  Lean for it.
- The two fields of `OsinLemma94PlanarPolygons D λ c ε K S`:
  - `side_budget : ∑ k, sideCount k ≤ K * Delta.rCellCount`. This is Lemma 9.3 ("`∑ n_i ≤ 53 n`")
    and (38) ("`k_i ≤ 4 n_i`") with one constant `K`.
  - `covers`: `∑_i |unboundDarts S.family i| ≤ ∑_k classWordLength (word k) (sideCount k)
    (relatorSides k)`. This is `S ≤ ∑ S_i`: every unbound dart of an `R`-cell lies on an (A1) side.
- Earlier item, CLOSED: `OsinLemma94AntiparallelMetricStatement`, by sec5-sentences
  (`osinLemma94AntiparallelMetric`, e3da1ba60, probe 0913-034427-9910 GREEN), on this lane's
  oriented layer below.
- `OsinLemma94RunInput` and `OsinLemma94Counting` are superseded. Their files stay on main
  untouched (82ba54dfb, GREEN 0913-010901-92003) and have no users.

## Plan (from main, before the name arrives)
- `side_budget`.
  - The arithmetic of Lemma 9.3 is on main. `lemma61_arcCount_le` (`Estimating/Unbound.lean`)
    gives `typeA12 + typeA3 ≤ 53 n` from `e ≤ 3(v − 1)`, `v ≤ n + r`, `r ≤ 4`,
    `typeA12 ≤ 2e + n + r` and `typeA3 ≤ 2e`.
  - `OsinLemma94PlanarRunInput` already assumes the Euler count
    `S.family.card ≤ 3 * (Delta.rCellCount + cuts.count - 1)`, and `SectionCuts.count_le` gives `r ≤ 4`.
  - What remains is to count the arcs of the component walks against `|M|`, `n` and `r`, and to
    bound the extra sides that cutting paths and corners add.
- `covers`.
  - `RegionCandidate.perimeter_eq` (`Estimating/RegionPartition.lean`) splits each cell perimeter
    into exterior-bound, interior-bound and unbound darts.
  - `false_of_unbound_shared_edge` (`Estimating/OsinUnboundSharedEdge.lean`, 8009a06ff) rules out an
    unbound dart that faces a relator cell or the exterior. It needs `LabelLegal`, `weight_maximal`,
    nontrivial relator words and a cell with more than one dart.
  - What remains is that the (A1) sides of the component walks carry the unbound darts with
    their lengths.

## On main (this lane)
- `GGT/OlshanskiiFirstVisit.lean` and `GGT/OlshanskiiOrientedLemma25.lean`: 1c5f36398, GREEN
  0913-023524-13449. These hold the first-visit witnesses and `exists_long_antiparallel_pair`, the
  antiparallel Lemma 25 for polygons with at most `2^c` sides.
- `GGT/OlshanskiiOrientedClasses.lean`: 0963dc2b4, GREEN 0913-025244-65395. `OrientedSidePair`,
  `OrientedClassPair`, and their restriction, rotation and cut transports.
- `GGT/OlshanskiiOrientedBisection.lean` and `GGT/OlshanskiiOrientedThreeClasses.lean`: 0ff430236,
  GREEN 0913-025900-86792. They hold `exists_orientedClassifiedBisection`,
  `exists_orientedClassPair_of_aggregate_all`, and the closed
  `orientedThreeClassPolygon : OrientedThreeClassPolygonStatement`. That is Lemma 3.7 with an
  antiparallel pair and the same constants.
- All five modules are in root-wire wave 3 (cdc493958).

## Duplicate draft, not landed
- I wrote a second proof of the same endpoint at the same path,
  `Estimating/OsinLemma94AntiparallelMetric.lean`. It picks a dense polygon from the side budget with
  `ρ' = ⌊ρ / (K + 1)²⌋`, runs an oriented `exists_polygonPair` on the geodesic replacement, then uses
  sec5-sentences' connectors. sec5-sentences landed e3da1ba60 at that path at 03:44:52, after my path
  check and before my landing.
- nmland refused the landing (clobber guard). From 03:47:39 my Write had replaced sec5-sentences'
  bytes in the shared tree. I restored origin's bytes (md5 f44ea282, equal to their `.0913-v1`
  backup) and dropped the path from `hull-count94.files`. My variant exists only in the lane backup.
- My variant built GREEN at probe 0913-035614-34211. That record lists the path with the variant's
  bytes (md5 d1e8e389), so it is not evidence for the landed file. The landed file's evidence is
  sec5-sentences' 0913-034427-9910.

## Finding behind the reassignment: the orientation gap
- `WordConnectorPair` fixes `a < a'` and leaves `b, b'` in either order. The planar Case 1
  (`false_of_quadrilateral_region`) contradicts only the antiparallel case `b' < b`. A parallel pair
  needs two crossing chords in a disc face.
- The unoriented metric chain loses the orientation in two places:
  - `SidePair` ("Orientation on either side is immaterial"), with `β ≤ |s' - s|` in Lemma 25;
  - the existential Morse index choice.
- Osin's printed Lemma 3.7 is unoriented. His Case 1 boundary `q1 s1 q2⁻¹ s2` uses the antiparallel
  form.

## Census
- The LINE:1636 row (thm:hull, Osin Lemma 9.4 inside Hull's proof) now follows the pieces route.
  It stays partial, and its residual is `OsinLemma94PlanarRunInput`.

## OsinUnboundSharedEdge triage (lead, ~04:10)
- Route check: nothing on the `osinLemma94Section_of_pieces` / `OsinLemma94PlanarRunInput` route
  imported `Estimating/OsinUnboundSharedEdge.lean`. As the lead instructed, this lane did no diagnosis
  and no fix.
- hull-unbound fixed the red itself: 8009a06ff, probe 0913-042440-98733 GREEN.

## Residual
- This lane owns no open Prop until hull-unbound's side_budget/covers Prop lands.
- The rest of `OsinLemma94PlanarRunInput` stays with hull-unbound. sec5-sentences takes a case and
  theoremc-retire takes C1.

## Next
- When the Lean name and file arrive: a new module of this lane, with the path checked on origin and
  on disk right before writing. The statement lands unverified first. Then the proof, a probe, the
  landing, a census row and the wire queue.

## Coordination
- hull-unbound owns `OsinLemma94Pieces`, `OsinUnboundSharedEdge` and `UnboundWordPolygonMonotone`.
- sec5-sentences owns `UnboundMonotoneMorseIndex`, `UnboundOrientedWordConnectors`,
  `UnboundOrientedWordPolygon` and `OsinLemma94AntiparallelMetric`.
