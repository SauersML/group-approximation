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

On origin/main the root imports Subdivided, RegionFaces, Phi, PhiCount, PhiBound and Hereditary,
and kh-ejz's `Estimating/OsinAppendixEulerMultigraph`. Count, Exterior, ExteriorCount and
EmptyTwoGon are not wired.

## Landings

- 44c6bab14, e4cb2d641, 864fdf3d2, f7a0fc32e, 1777a684a, cdd4b82df, 2cfa0c398: the seven Euler modules.
- 14d85b1d0, 30545e88a, fbef94518: this report.
- 9fdb800358088b2ba0b14717a16f16fd041f69f8: `CombMapRestrictionFaceClasses`.
  Probe 0913-032836-75226 green, md5 of the green record equal to origin/main, ancestor of main.
- 4e27d4965d3b6bc90312e1080a4d20abce59d18b: `OsinAppendixEulerExterior`.
  Probe 0913-044600-43289 green, md5 equal to origin/main, ancestor of main.
- 0508228436ea9d7aee9c324702401676b8cef61d: `OsinAppendixEulerExteriorCount`.
  Probe 0913-045049-59145 green with `BUILT`, md5 equal to origin/main, ancestor of main.
- 16d923f2780221c7eb733c90b6b2a962a4871bc4: `OsinAppendixEulerEmptyTwoGon`. Landed unverified,
  then probe 0913-061850-77139 green with `BUILT`, md5 equal to origin/main, ancestor of main.

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

## Residual

```lean
def PhiPrimeCountInput (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) : Prop :=
  ∀ (Delta : DiscDiagram.{u, w, v} W) (cuts : SectionCuts D lambda c Delta.boundaryWord),
    Delta.LeastArea → 0 < Delta.rCellCount →
      ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
        S.NoLoops → S.NoMultipleEdges →
          S.family.card ≤ 3 * (Delta.rCellCount + cuts.count - 1)
```

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

- **C1, C2.** Done: `phiMapO` is a `SubdividedMultigraph`, and linked regions give
  `|E| + 6 ≤ 3|V| + t`.
- **C3.** A face of `phiMapO` of degree less than six is a two-gon between two different regions
  `a`, `b` with the same pair of ends. `NoMultipleEdges` excludes two cells, so `a` and `b` are
  exterior regions of one cell.
- **C4.** Inject into the `r` corners every two-gon whose gap at `O` contains a corner.
- **C5.** Inject every other two-gon whose face class holds a relator cell into the components
  not linked to `O` and the isolated cells, through (J). Sum over the components with
  `card_le_of_endpoints`.
- **C6.** Stated as `EmptyTwoGonInput`.
- **Extraction.** From an empty two-gon of `phiMapO` to the hypotheses of `EmptyTwoGonInput`: the
  merged `PocketRegion`, the two arcs and the boundary equation. By the roster hull-euler builds it
  and consumes the region-side carrier (a).
- **Assembly.** `PhiPrimeCountInput` from `EmptyTwoGonInput`, then
  `OsinPhiPrimeCountSectionStatement`.

## Open questions to the lead

1. Does the carrier (a) cover two exterior regions of one cell (target `none`), or only regions
   between two cells?
2. Should `EmptyTwoGonInput` instead be the single shared merge Prop proposed by audit-sec5 for
   the inputs of `false_of_collapse_singleton` (MultipleEdgeCut, SectionPocketCut and C6)?

## Census

No rows yet. The rows wait for the closure of `PhiPrimeCountInput`, which carries the Euler count
inside the proof of `thm:hull` (tex 1636, through Osin's Lemma 9.7(a)).

## Next

C3, the two-gons of `phiMapO`.
