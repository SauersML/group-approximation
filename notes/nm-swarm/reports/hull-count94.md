# hull-count94

## Scope
- Item (lead, after the 08:30 restart): the PolygonCount piece of
  `osinLemma94Section_of_planarPieces`. That is `OsinLemma94PolygonCountInput` in
  `Estimating/OsinLemma94PlanarPieces.lean` (hull-unbound). This lane adopts that Prop and states
  no duplicate.
- The Prop is `P.SideBudget K ∧ P.Covers L` for maximal realized polygons of a dart-minimal optimal
  family.
- Ruling (ROSTER-0913, SideBudget spelling F1): `∃ K` moves after `∀ ε` in the count Prop and the
  metric Prop, and (A2) sides skip value-one excursions. This lane writes the rule 22 change.
- Helper: audit-intro. It proved the region-facing count and now checks pinched relator cells.

## Covers half: CLOSED
- `Estimating/OsinLemma94PolygonCovers.lean` (this lane), probe 0913-093648-12289 GREEN.
  - `OsinCCondition.listVal_ne_one_of_mem`: a `(λ, c)`-quasi-geodesic relator word of length
    `ρ > c / λ` does not have value one.
  - `GloballyDistinguishedSectionFamily.alpha_faceOf_not_cell_of_unbound`: the face across an unbound
    dart is no relator cell and not the exterior. It uses `false_of_unbound_shared_edge`.
  - `OsinLemma94RealizedPolygons.exists_relatorSide_of_unbound`: if that face is also in no selected
    region, it is a polygon face, and the reverse dart lies on a side of kind `cell`.
    - A boundary side would make the dart exterior.
    - A cutting side has the polygon face on both sides.
    - A short side has a selected region across it, and no region contains a cell.
  - `sum_card_unboundOffRegions_le`, then `covers_of_regionFacing_le`: `S ≤ ∑ S_i + (region-facing
    unbound darts)`.
- `Estimating/OsinLemma94RegionSideCount.lean` (audit-intro, 9d3013e41, GREEN 0913-091959-40244):
  `sum_card_regionFacingUnbound_le`, at most `2 ε |M|` region-facing unbound darts.
- `Estimating/OsinLemma94PolygonCount.lean` (this lane), same probe:
  - the closed endpoint `osinLemma94PolygonCoversInput : OsinLemma94PolygonCoversInput`, for every
    `ε`, with `L = 24 ε` and `ρ₀ = ⌈c / λ⌉₊ + 2`. It uses `|M| ≤ 3 (n + r - 1) ≤ 12 n` from `r ≤ 4`
    and `n ≥ 1`;
  - `osinLemma94PolygonCountInput_of_sideBudget : OsinLemma94PolygonSideBudgetInput →
    OsinLemma94PolygonCountInput`.

## F1 quantifier order (the first half of the ruling)
- `OsinLemma94AntiparallelMetricStatement` (`OsinLemma94Pieces`) is now
  `∃ ε₀, ∀ ε ≥ ε₀, ∀ K, ∃ ρ₀ > 0, ∀ ρ ≥ ρ₀, …`. Only the binder order of the proof in
  `OsinLemma94AntiparallelMetric` changes. `ε₀` comes from `unboundOrientedWordPolygonMonotone`
  before `K` is used, and `K` enters only `ρ₀ = (K + 1)² ρ₁`.
- `OsinLemma94PolygonCountInput` (`OsinLemma94PlanarPieces`) and
  `OsinLemma94PolygonSideBudgetInput` (`OsinLemma94PolygonCount`) are now
  `∃ ε₀, ∀ ε ≥ ε₀, ∃ K, …`.
- `osinLemma94Section_of_pieces`, `osinLemma94Section_of_planarPieces` and
  `osinLemma94PolygonCountInput_of_sideBudget` are adapted.
- Probe 0913-115846-46341 GREEN, all four modules BUILT.

## Residual
- `OsinLemma94PolygonSideBudgetInput` (in `OsinLemma94PolygonCount.lean`):
  `∃ ε₀, ∀ ε ≥ ε₀, ∃ K, ∃ ρ₀ > 0, ∀ ρ ≥ ρ₀, …, P.Maximal → ∑ k, P.sideCount k ≤ K n`.
- As stated it is over-strong. Model tests (reported to main):
  - Pockets. A region side of length at most `ε` touching a cell `s` times leaves `s` unselected
    `G`-faces, so `K` must come after `ε`. F1 fixes this.
  - Spurs. A spur on a section splits a boundary side. The ruled skip lets the side span it, but
    `Maximal`'s clause `facePerm (alpha e') ≠ alpha e` already allows the split at a spur base.
    So `Maximal` also needs a clause saying the two sides do not join into one skip-arc.
  - Boundary bubbles. `face_complete` makes every unselected `G`-face a polygon.
    - Model: `λ = 1/8`, `c = 3`, sections `r | (g·abc)^m | g^{-m}` with `abc = 1` in `G`.
    - The dart-minimal diagram carries `m` value-one bubbles on a spur tree, with no (A1) side and
      in no region, while `n = 1`.
    - Proposed: budget only the polygons with an (A1) side. Polygons without one have `S_i = 0`.
  - Pinched relator cells.
    - A relator with a value-one subword can pinch around an unselected `G`-face. That face is a
      polygon with one (A1) side, and the (A1) side across the stretch splits at the pinch.
    - `DartMinimal` does not see the pinch, since the dart count is unchanged.
    - Proposed exclusion: minimize faces after darts. audit-intro is checking the cases.
  - `cuts.count ≤ 4 ≤ 4 n`, so the sections are bounded by `n`.
- The skip also affects Case 1. `OsinLemma94CaseOneWalk`, `OsinLemma94CaseOneWalkHolds`,
  `OsinUnboundCaseOneRun` and `exists_quadrilateral_region` all consume contiguous target arcs.
  With a spur inside the window the contiguous walk statement is false.

## On main from earlier items
- `GGT/OlshanskiiFirstVisit.lean`, `GGT/OlshanskiiOrientedLemma25.lean` (1c5f36398),
  `GGT/OlshanskiiOrientedClasses.lean` (0963dc2b4), `GGT/OlshanskiiOrientedBisection.lean` and
  `GGT/OlshanskiiOrientedThreeClasses.lean` (0ff430236). These are the oriented Lemma 3.7 layer
  under `OsinLemma94AntiparallelMetricStatement` (closed by sec5-sentences, e3da1ba60). All five
  are in root-wire wave 3.
- `OsinLemma94RunInput` and `OsinLemma94Counting` (82ba54dfb) are superseded and have no users.
- A second proof of the antiparallel metric endpoint exists only in the lane backup. sec5-sentences
  landed first at the same path, and nmland's clobber guard refused mine.

## Census
- The LINE:1636 row (thm:hull, Osin Lemma 9.4 inside Hull's proof) stays partial. Its count
  residual is `OsinLemma94PolygonSideBudgetInput` (census row landed 4e7a84555).

## Next
- The second half of the ruling, after main rules on the new mechanisms: skip-arc (A2) sides, the
  `Maximal` skip clause, the A1-filtered budget and a pinch exclusion. These land together with
  the Case 1 users.
- Then prove the respelled side budget from the Lemma 9.3 counts on main (`PhiPrimeCountInput`,
  `CellFaceCountInput`).

## Coordination
- hull-unbound owns `OsinLemma94PlanarPieces`, `OsinLemma94Pieces`, `OsinUnboundSharedEdge` and
  `UnboundWordPolygonMonotone`.
- sec5-sentences owns `OsinLemma94DartMinimal` and `OsinLemma94AntiparallelMetric`.
- theoremc-retire owns `OsinLemma94CaseOneWalk` and `OsinUnboundCaseOneRun`; ko-closed owns
  `OsinLemma94CaseOneWalkHolds`.
- audit-intro owns `OsinLemma94RegionSideCount`.
