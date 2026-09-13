# hull-count94

## Scope
- Item (lead, after the 08:30 restart): the PolygonCount piece of
  `osinLemma94Section_of_planarPieces`. That is `OsinLemma94PolygonCountInput` in
  `Estimating/OsinLemma94PlanarPieces.lean` (hull-unbound, 80790fad1 and f2cc2be97). This lane adopts
  that Prop and states no duplicate.
- The Prop is `P.SideBudget K ∧ P.Covers L` for maximal realized polygons of a dart-minimal optimal
  family, with `K` chosen before `ε` and `L` after `ε`.
- Helper: audit-intro, which took the region-facing count.

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

## Residual
- `OsinLemma94PolygonSideBudgetInput` (in `OsinLemma94PolygonCount.lean`):
  `∃ K, ∃ ε₀, ∀ ε ≥ ε₀, ∃ ρ₀ > 0, ∀ ρ ≥ ρ₀, …, P.Maximal → ∑ k, P.sideCount k ≤ K n`.
- Risk, reported to main and awaiting a ruling. `DiscDiagram.inner_face` makes every polygon face a
  value-one face. Two things break a constant `K` chosen before `ε`.
  - A boundary side may follow any arc of `∂Δ` between cuts, and maximality splits sides. So an
    outer spur can add sides with no relator cell to charge them to.
  - Pockets between selected regions add short sides in proportion to `ε |M|`, not `|M|`.
- Proposed repair: (A2) sides skip value-one excursions, and `∃ K` moves after `∀ ε` in both the
  count Prop and the metric Prop. Rule 22 users on main: `OsinLemma94PlanarPieces` (hull-unbound)
  and `OsinLemma94CaseOneWalk` (theoremc-retire).

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
  residual is now `OsinLemma94PolygonSideBudgetInput`.

## Next
- Land the census row and the wire-queue line for the two modules.
- On the ruling: either prove `OsinLemma94PolygonSideBudgetInput` as stated, or land a refutation
  of the over-strong form and adapt with hull-unbound under rule 22.

## Coordination
- hull-unbound owns `OsinLemma94PlanarPieces`, `OsinLemma94Pieces`, `OsinUnboundSharedEdge` and
  `UnboundWordPolygonMonotone`.
- sec5-sentences owns `OsinLemma94DartMinimal` and `OsinLemma94AntiparallelMetric`.
- theoremc-retire owns `OsinLemma94CaseOneWalk`.
- audit-intro owns `OsinLemma94RegionSideCount`.
