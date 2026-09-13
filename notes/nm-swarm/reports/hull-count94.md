# hull-count94

## Scope
- Roster, Reassignments 09-13 (W1 h94): `OsinLemma94AntiparallelMetricStatement`
  (`Estimating/OsinLemma94Pieces.lean`, hull-unbound's file). It is the `hmetric` input of
  `osinLemma94Section_of_pieces`, which gives `OsinLemma94SectionStatement` (h94 of the assembly).
- CLOSED by sec5-sentences (roster ~03:55): `osinLemma94AntiparallelMetric` (e3da1ba60) on
  `unboundOrientedWordPolygonMonotone` (779509227), probe 0913-034427-9910 GREEN, both queued for
  wiring. That proof consumes this lane's oriented layer below.
- `OsinLemma94RunInput` and `OsinLemma94Counting` are superseded. Their files stay on main
  untouched (82ba54dfb, GREEN 0913-010901-92003) and have no users.

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
- Route check: nothing imports `Estimating/OsinUnboundSharedEdge.lean`.
  - No file under `GroupApproximation/` names the module, on origin/main or in the shared tree. The
    same grep does find the importer of `OsinLemma94Pieces`.
  - Its declarations `SectionCuts.exists_section_of_lt` and
    `RealizedSectionFamily.false_of_unbound_shared_edge` are used only inside the module, and no census
    row cites them.
  - So the `osinLemma94Section_of_pieces` / `OsinLemma94PlanarRunInput` route does not depend on it.
    As the lead instructed, there is no diagnosis and no fix.
- Disk differs from main.
  - origin has b52365364's 347 lines (md5 b6a6c77e). These are the red bytes of 0913-022343-56095 and
    of root-wire wave 1, equal to hull-unbound's `.red-0913-022343` backup.
  - The shared tree holds an unlanded 531-line rewrite (md5 82ea7352, mtime 09-13 04:16:41), listed
    only in `hull-unbound.files`. It splits the long proof into `digon_decomposition`,
    `false_of_digon_region`, `false_of_digon_toward_cell` and `false_of_digon_toward_outer`.
  - hull-unbound is probing that draft (0913-042440-98733, started 04:24:40), so it is fixing the red
    itself.
  - The landing condition "disk = main" does not hold. This lane stops and does not touch the file.

## Residual
- This lane owns no open Prop.
- `OsinLemma94PlanarRunInput` is the only other input of `osinLemma94Section_of_pieces`. hull-unbound
  owns it; sec5-sentences takes a case and theoremc-retire takes C1.

## Next
- The next item the lead names.

## Coordination
- hull-unbound owns `OsinLemma94Pieces` and `UnboundWordPolygonMonotone`.
- sec5-sentences owns `UnboundMonotoneMorseIndex`, `UnboundOrientedWordConnectors`,
  `UnboundOrientedWordPolygon` and `OsinLemma94AntiparallelMetric`.
