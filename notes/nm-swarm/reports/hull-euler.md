# hull-euler: the Euler count input of Osin's Lemma 9.7

Lane scope: `PhiPrimeCountInput` (`GroupApproximation/GGT/VanKampen/Estimating/OsinAppendixEulerCount.lean`),
the Euler count `|M| ≤ 3(n + r − 1)` of Osin's `Φ'_M` (arXiv:math/0411039v3, Appendix, Lemma 9.3).
`eulerCountInput_of_phiPrimeCount` (cdd4b82df) turns it into the `EulerCountInput` used by
`OsinSection97InputsStatement`. The section form is `OsinPhiPrimeCountSectionStatement`.

## Modules

| Module | Content | State |
|---|---|---|
| `Estimating/OsinAppendixEulerSubdivided` | `edgeBound_of_subdividedGraph` | green 0912-104426-41122 |
| `Estimating/OsinAppendixEulerRegionFaces` | faces of the region graph, `collapsedMap` | green 0912-104426-41122 |
| `Estimating/OsinAppendixEulerPhi` | `sideCell`, `cross`, `PhiData`, `phiMap` | green 0912-104426-41122 |
| `Estimating/OsinAppendixEulerPhiCount` | dart and vertex counts of `phiMap` | green 0912-104426-41122 |
| `Estimating/OsinAppendixEulerPhiBound` | `card_le_of_linked` | green 0912-104426-41122 |
| `Estimating/OsinAppendixEulerHereditary` | `card_le_of_endpoints`, `hasEndpointClosedPlanarEdgeBound_of_phiData` | green 0912-104426-41122 |
| `Estimating/OsinAppendixEulerCount` | `PhiPrimeCountInput`, `eulerCountInput_of_phiPrimeCount` | green 0912-104426-41122 |
| `CombMapRestrictionFaceClasses` | `CombMap.IsRestriction.faceOf_eq_of_faceClass` | green 0913-032836-75226 |
| `Estimating/OsinAppendixEulerExterior` | `sideCellO`, `crossO`, `ExtPhiData`, `phiMapO`, `phiSubdividedMultigraphO` | green 0913-044600-43289 |
| `Estimating/OsinAppendixEulerExteriorCount` | `phiMapO_dartCount`, `phiMapO_vertexCount_le`, `phiMapO_planar`, `card_add_six_le_of_linkedO` | green 0913-045049-59145 |
| `Estimating/OsinAppendixEulerEmptyTwoGon` | `EmptyTwoGonInput`, the piece Prop of C6 | green 0913-061850-77139 |
| `Estimating/OsinAppendixEulerExteriorTwoGon` | `phiO_alpha`, `sideCellO_facePerm_facePerm`, `exterior_of_isTwoGon` (C3) | green 0913-065054-20285 |
| `Estimating/OsinAppendixEulerSmallFaces` | C6′ `TwoGonHoldsInput`, `faceOf_eq_of_faceClassO`, `phiPrimeCountInput_of_smallFaces` from C4, C5, C6′ | green 0913-093143-91859 |

The lane consumes three peer modules:

- ghw-charp2's `Estimating/OsinAppendixEulerExteriorLinked` (cbca8029b): `linkedComponentO`,
  `endCellsO`, `ExtPhiData.mono`, `linked_linkedComponentO`, `card_add_six_le_linkedComponentO`.
- leavitt-units' `Estimating/OsinAppendixEulerCornerTwoGon` (d0a41c1da): C4.
- hs-vanishes' `Estimating/OsinAppendixEulerExteriorCellFaces` (bdd687708): C5.

On origin/main the root imports Subdivided, RegionFaces, Phi, PhiCount, PhiBound and Hereditary,
and kh-ejz's `Estimating/OsinAppendixEulerMultigraph`. Count, Exterior, ExteriorCount,
EmptyTwoGon, ExteriorTwoGon and SmallFaces are not wired.

## Landings

- 44c6bab14, e4cb2d641, 864fdf3d2, f7a0fc32e, 1777a684a, cdd4b82df, 2cfa0c398: the seven Euler modules.
- 14d85b1d0, 30545e88a, fbef94518, 0eb25c129, cae852232: this report.
- 9fdb800358088b2ba0b14717a16f16fd041f69f8: `CombMapRestrictionFaceClasses`.
  Probe 0913-032836-75226 green, md5 of the green record equal to origin/main, ancestor of main.
- 4e27d4965d3b6bc90312e1080a4d20abce59d18b: `OsinAppendixEulerExterior`.
  Probe 0913-044600-43289 green, md5 equal to origin/main, ancestor of main.
- 0508228436ea9d7aee9c324702401676b8cef61d: `OsinAppendixEulerExteriorCount`.
  Probe 0913-045049-59145 green with `BUILT`, md5 equal to origin/main, ancestor of main.
- 16d923f2780221c7eb733c90b6b2a962a4871bc4: `OsinAppendixEulerEmptyTwoGon`. Landed unverified,
  then probe 0913-061850-77139 green with `BUILT`, md5 equal to origin/main, ancestor of main.
- c48f20f4121ed4d6d5c176d2acfaa27dae156b8e: `OsinAppendixEulerExteriorTwoGon`. Landed unverified,
  then probe 0913-065054-20285 green with `BUILT`, md5 equal to origin/main, ancestor of main.
- 2279167e63a75b1dc68b89a2a2de8e8f141dafd4: `OsinAppendixEulerSmallFaces`, first form, with
  duplicate C4/C5 counts. Probe 0913-090235-64116 green with `BUILT`, ancestor of main.
- 4beca2743bf6284a875a84b1149f3117d46dd1e6: `OsinAppendixEulerSmallFaces` restated over the peer C4
  and C5, with C6′ as `TwoGonHoldsInput`. Probe 0913-093143-91859 green with `BUILT` (base
  800254639), md5 of the green record equal to the landed file, ancestor of main. Backup
  `backup/hull-euler/OsinAppendixEulerSmallFaces.lean.0913b` holds the first form.

## Residual Props

`phiPrimeCountInput_of_smallFaces` (`Estimating/OsinAppendixEulerSmallFaces.lean`):

```lean
theorem phiPrimeCountInput_of_smallFaces
    (hcorner : CornerTwoGonInput.{u, w, v} D lambda c eps W)
    (hcell : CellFaceCountInput.{u, w, v} D eps W)
    (hholds : TwoGonHoldsInput.{u, w, v} D lambda c eps W) :
    PhiPrimeCountInput.{u, w, v} D lambda c eps W
```

| Prop | Module, SHA | Lane | State |
|---|---|---|---|
| `CornerTwoGonInput` (C4) | `OsinAppendixEulerCornerTwoGon`, d0a41c1da | leavitt-units | stated, compiles as an import in 0913-093143-91859 |
| `CellFaceCountInput` (C5) | `OsinAppendixEulerExteriorCellFaces`, bdd687708 | hs-vanishes | stated, green record 0913-090700-76588 |
| `TwoGonHoldsInput` (C6′) | `OsinAppendixEulerSmallFaces`, 4beca2743 | debt-conditional | stated, green record 0913-093143-91859 |
| `EmptyTwoGonInput` (C6) | `OsinAppendixEulerEmptyTwoGon`, 16d923f27 | fff-periodic | proved: `emptyTwoGonInput_holds` (2aa17abb0) |

`emptyTwoGonInput_holds` (`Estimating/OsinPocketDiscEmptyTwoGon.lean`) takes no Prop hypothesis.
Probe record `fff-periodic.green.0913-091627-32913` reads `PROBE GREEN`, and its md5 equals the
file on origin/main. The earlier record `0913-090831-85897` reads `PROBE FAILED rc=1`.

The statements, with `C := linkedComponentO E a₀` over `S.diagram`:

- **C4.** For every `S` and every `P : ExtPhiData S.family E`, at most `cuts.count` faces `f` of
  `phiMapO S.family E` satisfy `(phiSubdividedMultigraphO P).IsTwoGon f` and
  `GapAtOHoldsCorner cuts S.family E f`. The assembly applies it at `E := C`, `P := P.mono`.
- **C5.** For `ExtPhiData family E`, no two regions of `E` joining the same two cells, and
  `a₀ ∈ E` with target `none`:
  `|E| + 3·#{f | HoldsCellO family C f} ≤ |C| + 3·#{i | some i ∉ endCellsO C}`.
- **C6′.** Take a least-area `Δ`, a globally distinguished `S` without loops or multiple edges,
  `a₀ ∈ S.family` with target `none`, `P : ExtPhiData S.family C` and a face `f` of
  `phiMapO S.family C`. Suppose `f` is a two-gon, `¬GapAtOHoldsCorner cuts S.family C f` and
  `¬HoldsCellO S.family C f`. Then `False`.

The assembly. Let `F = S.family`, `V = endCellsO C`, `t` the faces of degree less than six, `T`
the two-gons with a corner in the gap, `H` the faces holding a cell and `N` the non-end cells.

- `|C| + 6 ≤ 3|V| + t` (`card_add_six_le_linkedComponentO`).
- `N + |V| ≤ n + 1`, since `V` has at most one element that is not `some`.
- If `|C| ≥ 2`, `phiMapO` has `4|C| > 4` darts and is connected, so every small face is a two-gon
  (`isTwoGon_of_faceDegree_lt_six`). By C6′, `t ≤ T + H`. By C4, `T ≤ r`. By C5,
  `|F| + 3H ≤ |C| + 3N`. So `|F| ≤ 3n + r − 3`.
- If `|C| ≤ 1`, `V` holds `some a₀.source` and `none`, and C5 gives `|F| ≤ 3n − 2`.
- Without an exterior region every region joins two cells, and `card_le_of_endpoints` on all
  cells gives `|F| ≤ 3(n − 1)`.

In every case `|F| ≤ 3(n + r − 1)`.

Why C6′ holds, the route for debt-conditional:

- A two-gon through a cell `i` has two different regions `a`, `b` of `C`. If the second vertex is
  a cell, `a` and `b` join the same two cells, against `S.NoMultipleEdges`.
- Otherwise `a` and `b` are exterior regions of `i` (C3, `exterior_of_isTwoGon`). With no corner
  in the gap, `a` and `b` target one section.
- A cell inside the pocket that is an end of `C` would be a vertex inside the face `f`. So with
  `¬HoldsCellO`, the pocket holds no relator cell. A region outside `C` has no end on the pocket,
  so it avoids it. `EmptyTwoGonInput` then gives `False`.
- Truth check: `GapAtOHoldsCorner` reads the gap after `phiRegionO y` and before the region two
  steps on around the face. That must be the gap inside `f`, or C6′ fails. C4 counts the same
  predicate, so the assembly does not see the orientation.

## C6: the empty two-gon

`EmptyTwoGonInput D lambda c eps W` (`Estimating/OsinAppendixEulerEmptyTwoGon.lean`). Take:

- a least-area diagram and a distinguished system `S`;
- two different regions `a`, `b` of `exteriorAt S.family i` that both target section `j`;
- a `PocketRegion` `P` of `S.diagram` that contains `a.1` and `b.1`, holds no relator cell and
  meets no other selected region;
- an arc `source` of `cellDarts i` with `a.s + b.s ≤ source.length`;
- an arc `target` of the boundary from the start of `a`'s target arc to the end of `b`'s, with
  `a.t + b.t ≤ target.length`.

If `invDarts P.outer.cycle = source.reverseDarts ++ a.2.rightSide ++ target.darts ++ b.2.leftSide`,
the Prop gives `False`. This is the proof of Osin's Lemma 9.7(a), osin 1731–1733: "otherwise one
can include the ε-contiguity subdiagrams corresponding to the edges e and f of Φ′M into a single
ε-contiguity subdiagram in the obvious way, contrary to the definition of M."

`FollowsBoundary` ruling (lead's question, from nm-endpoints): option 2, and the Prop is unchanged.

- Route A (`emptyTwoGonInput_holds`) uses no `FollowsBoundary` hypothesis, and it intros the
  binders by position, so a new binder would break it.
- A consumer that needs `hwalk` for `InnerGRegion.ofPocketRegion` or `toInnerGRegion` builds `P`
  as `PocketRegion.ofSimpleClosedWalk`. `ofSimpleClosedWalk_followsBoundary` then gives `hwalk`.

fff-periodic and nm-endpoints have been told.

## Plan: Lemma 9.3 with one merged outer vertex

`O` is the dual vertex of the outer face of `Δ`. All sections meet there.

- **C1, C2, C3.** Done: `phiMapO` is a `SubdividedMultigraph`, linked regions give
  `|C| + 6 ≤ 3|V| + t`, and the two-gons are exterior pairs of one cell.
- **C4, C5.** Stated by leavitt-units and hs-vanishes. The assembly consumes them as stated.
- **C6′.** `TwoGonHoldsInput`, stated here in the vocabulary of C4 and C5. debt-conditional
  proves it.
- **C6.** `EmptyTwoGonInput`, proved by fff-periodic.
- **Assembly.** `phiPrimeCountInput_of_smallFaces`, then `OsinPhiPrimeCountSectionStatement`.

## Census

No rows yet. The rows wait for the closure of `PhiPrimeCountInput`, which carries the Euler count
inside the proof of `thm:hull` (tex 1636, through Osin's Lemma 9.7(a)).

## Next

1. When C4, C5 and C6′ are proved, close `PhiPrimeCountInput` through
   `phiPrimeCountInput_of_smallFaces`, with `#audit_closed_axioms` on the endpoint.
2. Then `OsinPhiPrimeCountSectionStatement`, and the census rows.
