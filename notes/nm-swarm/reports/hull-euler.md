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

None of these modules is wired to the root. kh-ejz's `Estimating/OsinAppendixEulerMultigraph`
(69c4c69da, 04240bd43) provides the Euler count with two-gons, and this lane consumes it.

## Landings

- 44c6bab14, e4cb2d641, 864fdf3d2, f7a0fc32e, 1777a684a, cdd4b82df, 2cfa0c398: the seven Euler modules.
- 14d85b1d0, 30545e88a: this report.
- 9fdb800358088b2ba0b14717a16f16fd041f69f8: `CombMapRestrictionFaceClasses`.
  - Landed unverified.
  - Probe 0913-032836-75226 was green, and the md5 of the green record equals the md5 on origin/main.
  - The commit is an ancestor of origin/main.

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
edges that are not retained never passes between two different faces of the restriction. The proof
grows the restriction one actual edge at a time:

- an added edge between different faces joins them;
- an added edge on one face is a spur, since otherwise deleting it would raise the Euler
  characteristic above two.

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

## Plan: Lemma 9.3 with one merged outer vertex

`O` is the dual vertex of the outer face of `Δ`. All sections meet there.

- **C1.** The exterior map `Φ''`. Generalize `cross` to `target = none`: for an exterior region the
  retained dart at `O` is `alpha` of the head of the target arc, since `targetBoundaryDarts none`
  is the arc itself. Restrict the dual of `collapsedMap` to the regions linked to `O`, and give the
  result a `SubdividedMultigraph` instance.
- **C2.** Take `m + 6 ≤ 3c + t` from kh-ejz's `edgeBound_of_subdividedMultigraph`.
- **C3.** A face of degree less than six is a two-gon `Π–a–O–b` with `a ≠ b` exterior regions of
  one cell. `NoMultipleEdges` excludes two-gons between two cells.
- **C4.** Inject into the `r` corners every two-gon whose gap at `O` contains a corner. This uses
  `RespectsSections` and nondegenerate arcs.
- **C5.** Inject every other two-gon whose face class holds a cell into the components not linked
  to `O` and the isolated cells, using (J). The darts of a component that is not retained are all
  connected by `FaceClassStep`, because `sigma = facePerm ∘ alpha`. Sum over the components with
  `card_le_of_linked`.
- **C6.** An empty two-gon gives `False`. Such a two-gon has two exterior regions `a ≠ b` of one
  cell, consecutive at `O` in one section, with no relator cell in its face class. The proof merges
  `a` and `b` against `card_minimal` through `false_of_collapse_singleton`
  (`OsinAppendixCutMerge.lean:120`).
- **Assembly.** With `k4 ≤ r + (components) + (isolated cells)`, the per-component bounds sum to
  `|M| ≤ 3(n + r − 1)`.

C1 to C5 need nothing from other lanes. C6 needs the pocket between `a` and `b` as a disc region
carrying a `ContiguityGeometry` for the merged region: the W1 (a) carrier (`IsDiscRegion` plus
`DiscDiagram.ofPlanar`) and kh-ejz's pocket geometry from `a ≠ b`. By the roster, hull-euler
consumes that carrier and does not build it. I have asked the lead whether hull-euler may state a
named piece Prop for the empty-pocket merge.

## Census

No rows yet. (J) carries no printed sentence. The rows wait for the closure of
`PhiPrimeCountInput`, which carries the Euler count inside the proof of `thm:hull` (tex 1636,
through Osin's Lemma 9.7(a)).

## Next

C1, the exterior crossings and the `O`-linked restriction.
