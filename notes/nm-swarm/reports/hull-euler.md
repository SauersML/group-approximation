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
| `Estimating/OsinAppendixEulerSmallFaces` | C4, C5, C6′ as named Props, `phiPrimeCountInput_of_smallFaces` | green 0913-090235-64116 |

The lane also consumes ghw-charp2's `Estimating/OsinAppendixEulerExteriorLinked` (cbca8029b):
`linkedComponentO`, `endCellsO` and `card_add_six_le_linkedComponentO`.

On origin/main the root imports Subdivided, RegionFaces, Phi, PhiCount, PhiBound and Hereditary,
and kh-ejz's `Estimating/OsinAppendixEulerMultigraph`. Count, Exterior, ExteriorCount,
EmptyTwoGon, ExteriorTwoGon and SmallFaces are not wired.

## Landings

- 44c6bab14, e4cb2d641, 864fdf3d2, f7a0fc32e, 1777a684a, cdd4b82df, 2cfa0c398: the seven Euler modules.
- 14d85b1d0, 30545e88a, fbef94518, 0eb25c129: this report.
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
- 2279167e63a75b1dc68b89a2a2de8e8f141dafd4: `OsinAppendixEulerSmallFaces`. Landed unverified,
  then probe 0913-090235-64116 green with `BUILT`, md5 equal to origin/main, ancestor of main.

## The face-class lemma (J)

```lean
def CombMap.FaceClassStep (M : CombMap) (keep : M.Dart → Prop) (x y : M.Dart) : Prop :=
  y = M.facePerm x ∨ (¬ keep x ∧ y = M.alpha x)

theorem CombMap.IsRestriction.faceOf_eq_of_faceClass (h : M.IsRestriction N e)
    (hM : M.IsPlanar) (hN : N.IsConnected) {d d' : N.Dart}
    (hp : Relation.EqvGen (FaceClassStep M (· ∈ Set.range e)) (e d) (e d')) :
    N.faceOf d = N.faceOf d'
```

Take a connected restriction of a planar map. Advancing around ambient faces and crossing ambient
edges that are not retained never passes between two different faces of the restriction.

At `phiMapO` this is `faceOf_eq_of_faceClassO`: a face class `FaceClassO family E` of the
collapsed map lies in one face of `Φ'_M` when the regions of `E` are linked.

## Residual: the three counts of the small faces

`phiPrimeCountInput_of_smallFaces` (`Estimating/OsinAppendixEulerSmallFaces.lean`) proves
`PhiPrimeCountInput` from three Props. They share these hypotheses:

```lean
∀ (Delta : DiscDiagram.{u, w, v} W) (cuts : SectionCuts D lambda c Delta.boundaryWord),
  Delta.LeastArea →
    ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
      S.NoLoops → S.NoMultipleEdges →
        ∀ a₀ ∈ S.family, a₀.2.target = none → ...
```

With `E := linkedComponentO S.family a₀`, the conclusions are:

| Prop | Conclusion | Lane |
|---|---|---|
| `CornerFacesInput` (C4) | `(cornerFacesO cuts S.family E).card ≤ 2 * cuts.count` | leavitt-units |
| `CellFacesInput` (C5) | `(cellFacesO S.family E).card + (outsideO S.family E).card + 3 * (endCellsO E).card ≤ 3 * S.diagram.rCellCount + 3` | hs-vanishes |
| `SmallFaceHoldsInput` (C6′) | `∀ f ∈ smallFacesO S.family E, HoldsCornerO cuts S.family E f ∨ HoldsCellO S.family E f` | debt-conditional, from `EmptyTwoGonInput` |

The definitions, all in namespace `Embedded.RegionCandidate`:

- `smallFacesO family E`: the faces of `phiMapO family E` of degree less than six.
- `FaceClassO family E`: `EqvGen (FaceClassStep (collapsedMap family).dual (PhiKeepO family E))`.
- `ClassMeetsO family E x f`: a dart of `phiMapO family E` on `f` lies in the class of `x`.
- `HoldsCellO family E f`: for a cell `i` with `some i ∉ endCellsO E`, the class of a collapsed
  dart on the face of `i` meets `f`.
- `HoldsCornerO cuts family E f`: for some `k : Fin cuts.count`, let `d` be the dart of
  `outerDarts Delta` at `cuts.cut k.castSucc % length`. The class of a collapsed dart at an end
  of `d` meets `f`.
- `cornerFacesO`, `cellFacesO`: the small faces that satisfy `HoldsCornerO` or `HoldsCellO`.
- `outsideO family E`: `family \ E`.

The assembly. Let `F = S.family`, `V = endCellsO E` and `T = smallFacesO F E`.

- `|E| + 6 ≤ 3|V| + |T|` (`card_add_six_le_linkedComponentO`).
- `|T| ≤ corner + cell` (C6′).
- `corner ≤ 2r` (C4).
- `cell + |F \ E| + 3|V| ≤ 3n + 3` (C5).

So `|F| ≤ 3n + 2r − 3 ≤ 3(n + r − 1)`. Without an exterior region every region joins two cells,
and `card_le_of_endpoints` on all cells gives `|F| ≤ 3(n − 1)`.

Why each Prop holds:

- **C4.** The kept darts of the collapsed map at one vertex of `Δ` form one orbit of its
  rotation, so one face class. By `faceOf_eq_of_faceClassO` a class meets at most one face. There
  are `r` cut darts, each with two ends.
- **C5.** `V` contains `none`, the outer end of `a₀`, so the claim is
  `cell + |F \ E| + 3|V_cells| ≤ 3n`. A region outside `E` joins two cells not in `V`, since an
  exterior region shares `none` with `a₀`. The cells not in `V` and the regions outside `E` split
  into `m` components with `m_i` cells, and `Σ m_i = n − |V_cells|`. Each component lies in one
  face class, so the cell faces inject into the components. `card_le_of_endpoints` bounds the
  regions of a component by `3(m_i − 1)`. Summing gives
  `cell + |F \ E| ≤ m + 3Σ(m_i − 1) ≤ 3(n − |V_cells|)`.
- **C6′.** By C3 (`exterior_of_isTwoGon`), a small face is one of two things. It is a two-gon
  between two different exterior regions `a`, `b` of one cell, or it is the only face when
  `|E| = 1`, and then the corner at `k = 0` holds it. On the side of `f`, the last target vertex
  of `a`, the gap and the first target vertex of `b` lie in the class of `f`. If `f` holds no
  corner, `a` and `b` target one section and the merged target arc respects the cuts. If `f` also
  holds no cell, the pocket holds no relator cell and meets no other selected region.
  `EmptyTwoGonInput` then gives `False`.

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

The carrier is the merged region, not the pocket between `a` and `b`, so two regions sharing a
side and pinched pockets are covered. It is true through `false_of_collapse_singleton`
(`OsinAppendixCutMerge.lean:120`) with `absorbed = {a, b}`:

- `R` comes from `P`;
- `H` has the four pieces of the equation;
- `hrespects` holds because `target` runs from `a`'s start to `b`'s end inside section `j`;
- `hsource` and `htarget` come from `S.nondegenerate`;
- `hweight` comes from the two length bounds.

By the roster, kh-ejz and hull-select discharge it.

## Plan: Lemma 9.3 with one merged outer vertex

`O` is the dual vertex of the outer face of `Δ`. All sections meet there.

- **C1, C2, C3.** Done: `phiMapO` is a `SubdividedMultigraph`, linked regions give
  `|E| + 6 ≤ 3|V| + t`, and the two-gons are exterior pairs of one cell.
- **C4, C5, C6′.** Stated as `CornerFacesInput` (leavitt-units), `CellFacesInput` (hs-vanishes)
  and `SmallFaceHoldsInput` (debt-conditional, from `EmptyTwoGonInput`).
- **C6.** Stated as `EmptyTwoGonInput`. By the lead's ruling it stays C6's interface.
- **Assembly.** `phiPrimeCountInput_of_smallFaces`, then `OsinPhiPrimeCountSectionStatement`.

## Open questions to the lead

1. Does the carrier (a) cover two exterior regions of one cell (target `none`), or only regions
   between two cells? It bears on the discharge of `EmptyTwoGonInput`, not on its statement.

## Census

No rows yet. The rows wait for the closure of `PhiPrimeCountInput`, which carries the Euler count
inside the proof of `thm:hull` (tex 1636, through Osin's Lemma 9.7(a)).

## Next

1. Get the SmallFaces probe green, then land plainly.
2. When C4, C5, C6′ and `EmptyTwoGonInput` are proved, close `PhiPrimeCountInput` through
   `phiPrimeCountInput_of_smallFaces`, with `#audit_closed_axioms` on the endpoint.
