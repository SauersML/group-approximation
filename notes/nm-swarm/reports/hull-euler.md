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
| `Estimating/OsinAppendixEulerSection` | `OsinCornerTwoGonSectionStatement`, `OsinTwoGonHoldsSectionStatement`, `osinPhiPrimeCountSection_of_pieces` | green 0913-125857-40608 |
| `NoncrossingClosedWalkEuler` | `IsNoncrossingClosedWalk.reclosed_euler`, `innerDiscRegion` (R2) | green 0913-150114-7274 |

The lane consumes three peer modules:

- ghw-charp2's `Estimating/OsinAppendixEulerExteriorLinked` (cbca8029b): `linkedComponentO`,
  `endCellsO`, `ExtPhiData.mono`, `linked_linkedComponentO`, `card_add_six_le_linkedComponentO`.
- leavitt-units' `Estimating/OsinAppendixEulerCornerTwoGon` (d0a41c1da): C4. It is proved by
  `cornerTwoGonInput` (`Estimating/OsinAppendixEulerCornerTwoGonCount`, 90245333d) and at section
  level by `osinCornerTwoGonSection` (`Estimating/OsinAppendixEulerCornerTwoGonSection`, 0c42391c2).
- hs-vanishes' `Estimating/OsinAppendixEulerExteriorCellFaces` (a6a2cadda): C5 and its proof
  `cellFaceCountInput`.

On origin/main (root 141bea9e6) the root imports Subdivided, RegionFaces, Phi, PhiCount, PhiBound,
Hereditary, EmptyTwoGon, ExteriorTwoGon and SmallFaces. It also imports the peer modules
ExteriorLinked, CornerTwoGon and ExteriorCellFaces, and kh-ejz's
`Estimating/OsinAppendixEulerMultigraph`. Count, Exterior, ExteriorCount and
`CombMapRestrictionFaceClasses` are reachable through SmallFaces. `OsinAppendixEulerSection` is
queued (wire-queue lines 626–627), and leavitt-units' Count and Section modules at lines 638–639.

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
- d1f3ebca1, 592caafdc, e84468da9, 960fd8d0c, e7df42eea: this report.
- 6401c70a6f64c4ecde540afcb41da9f1242c6ef6: `OsinAppendixEulerSection`, the section-level
  assembly with C4 and C6′ as named binders (lead's item, 09-13). Landed unverified, then probe
  0913-125857-40608 green with `BUILT` (base 711c053f1). All 13 overlay md5s equal origin/main,
  ancestor of main. Queued at wire-queue lines 626–627.
- 06c57ca01: this report.
- 7e254eb6600c31972da6291b7467b5ab06c9d6e8: `NoncrossingClosedWalkEuler`, the R2 Euler lemma.
  Landed unverified. Probe 0913-145807-90519 failed at one application: at the pin
  `List.next_mem` takes `l` and `x` explicitly.
- 19866c7d67ab262fb65d70770ab905136dd9fce1: the fix, landed unverified. Probe 0913-150114-7274
  green with `BUILT` (base 19866c7d6), no errors or warnings, all six `#audit_axioms` inside the
  classical allowlist. The md5 of the green record equals origin/main, and the commit is an
  ancestor of main.

## Residual Props

At section level (`Estimating/OsinAppendixEulerSection.lean`, 6401c70a6, green 0913-125857-40608):

```lean
theorem osinPhiPrimeCountSection_of_pieces
    (hcorner : OsinCornerTwoGonSectionStatement.{u, w, v})
    (htwogon : OsinTwoGonHoldsSectionStatement.{u, w, v}) :
    OsinPhiPrimeCountSectionStatement.{u, w, v}
```

| Prop | Lane | State |
|---|---|---|
| `OsinCornerTwoGonSectionStatement` (C4 uniformly) | leavitt-units | proved: `osinCornerTwoGonSection` (0c42391c2), checked 09-13 |
| `OsinTwoGonHoldsSectionStatement` (C6′ uniformly) | debt-conditional | stated, told the exact form 09-13 |

`osinCornerTwoGonSection` (`Estimating/OsinAppendixEulerCornerTwoGonSection.lean`) takes `ε₀ = 0`
and `ρ₀ = 1` over `cornerTwoGonInput D lambda c eps W`
(`Estimating/OsinAppendixEulerCornerTwoGonCount.lean`). Checked 09-13 against origin/main
50b6cbb9d:

- 90245333d and 0c42391c2 are ancestors of main;
- records `leavitt-units.green.0913-130413-64412` and `.0913-130704-80770` read `PROBE GREEN` and
  name the module under `# mods`, and their md5s equal the files on main;
- `OsinAppendixEulerCornerTwoGon.lean` is unchanged since d0a41c1da, and `OsinAppendixEulerSection`
  since 6401c70a6;
- neither file has `sorry`, `axiom` or `native_decide`, and both theorems carry `#audit_axioms`.

So the closure waits only on `OsinTwoGonHoldsSectionStatement`.

Both binders use the quantifier prefix of `OsinPhiPrimeCountSectionStatement`
(`Estimating/OsinAppendixGreendlingerPocketParts.lean:43`). They conclude
`CornerTwoGonInput D lambda c eps W` and `TwoGonHoldsInput D lambda c eps W`. Inside,
`phiPrimeCountInput_of_smallFaces` takes `hcell := cellFaceCountInput D eps W`. `ε₀` and `ρ₀` are
the maxima of the two thresholds. A producer module must import SmallFaces or
`OsinAppendixEulerSection` and must not be imported by SmallFaces. nm-endpoints fills `hcount` of
`relativeGreendlingerQuasiGeodesicLeastArea_of_pocketParts` with this theorem.

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
| `CornerTwoGonInput` (C4) | `OsinAppendixEulerCornerTwoGon`, d0a41c1da | leavitt-units | proved: `cornerTwoGonInput` (90245333d), green record 0913-130413-64412 |
| `CellFaceCountInput` (C5) | `OsinAppendixEulerExteriorCellFaces`, a6a2cadda | hs-vanishes | proved: `cellFaceCountInput`, green record 0913-100213-68371 |
| `TwoGonHoldsInput` (C6′) | `OsinAppendixEulerSmallFaces`, 4beca2743 | debt-conditional | stated, green record 0913-093143-91859 |
| `EmptyTwoGonInput` (C6) | `OsinAppendixEulerEmptyTwoGon`, 16d923f27 | fff-periodic | proved: `emptyTwoGonInput_holds` (2aa17abb0) |

`emptyTwoGonInput_holds` (`Estimating/OsinPocketDiscEmptyTwoGon.lean`) takes no Prop hypothesis.
Probe record `fff-periodic.green.0913-091627-32913` reads `PROBE GREEN`, and its md5 equals the
file on origin/main. The earlier record `0913-090831-85897` reads `PROBE FAILED rc=1`.

`cellFaceCountInput (D) (eps) (W) : CellFaceCountInput D eps W`
(`Estimating/OsinAppendixEulerExteriorCellFaces.lean`, a6a2cadda) also takes no Prop hypothesis.
Checked 0913:
- Probe record `hs-vanishes.green.0913-100213-68371` reads `PROBE GREEN`, and its md5 equals the
  file on origin/main.
- The definitions of `CellFaceCountInput` and `HoldsCellO` are the same as in bdd687708.
- The file has no `sorry`, `axiom` or `native_decide`, and the theorem carries `#audit_axioms`.
- The new import `OsinAppendixEulerHereditary` was already visible to SmallFaces through
  `OsinAppendixEulerCount`. So SmallFaces needs no new probe.

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
  so it avoids it. `EmptyTwoGonInput` then gives `False`, once there is a `PocketRegion` whose
  complement cycle reads `source.reverseDarts ++ a.rightSide ++ target.darts ++ b.leftSide`.
- audit-sec3's verdict (09-13): C6′ is true as stated and the orientation is right, but it is not
  proved. No landed theorem has type `TwoGonHoldsInput`. Over `S.diagram` no such `PocketRegion`
  exists in three configurations:
  - (a) A backtrack of section `j` between the targets. Its darts have the outer face on both
    sides. Copy: hs-vanishes' spur thickening.
  - (b) An edge of the source gap with cell `i` on both sides. Copy: `FaceEdgeDoubling` on cell
    `i`. `SurgeryFaceEdgeDoublingRegions` carries every region.
  - (c) `a.rightSide` and `b.leftSide` share an edge behind cell `i`, so the union is an annulus.
    Copy: `FaceEdgeDoubling` in the face of `a` at the shared edge, which leaves a pinched disc.
    The Regions transport carries only regions that avoid the doubled face and the face across it,
    so `a` and `b` need their own transport.
  - Ruling (B) (bdc7337fd) names only (a) and (b). Checked 09-13.
  - Owners (lead, 09-13): hs-vanishes has (a). leavitt-units has (b) and the transport for (c).
    sec2-sentences has the kept cell on the copy. debt-conditional keeps C6′ and assembles the
    pieces.
  - No landed declaration builds a `PocketRegion` from a pinched walk.
    `noncrossingClosedWalkSides` (26a7858f2) concludes only two `BoundaryCycle`s, and
    `bothFollowUnpinched` (74d4ebd34) needs `FollowsBoundary` on both cycles. Checked 09-13.
  - The turning condition for the pocket walk is open (kh-ejz).
  - Both optimality clauses range over every realized family of `Delta`, so the contradiction
    carries over from a copy.
  - debt-conditional's `OsinAppendixEulerTwoGonLabels` (81cb719d3, landed unverified) reads the
    labels `i`, `j`, `a`, `b` of `EmptyTwoGonInput` off the two-gon.
- Orientation, checked 0913: `GapAtOHoldsCorner` reads the gap inside `f`.
  - `CombMap.facePerm = sigma * alpha`, `dual.sigma = facePerm`, and `phiMapO` rotates by first
    return. So at `O` its rotation follows `Delta`'s face permutation around the outer face.
  - For a two-gon through `y` at `O`, the dart of `a = phiRegionO y` at `O` is `sigma` of the dart
    of `b = phiRegionO (facePerm (facePerm y))`. So the corner of `f` at `O` runs from the crossing
    of `b` to the crossing of `a` in face-permutation order.
  - `FaceBoundary.chain` lists the outer face in face-permutation order. `outerDarts` reverses it,
    and `boundaryWord`, the arc starts and `cuts.cut` all index `outerDarts`. So the corner reads
    forwards from the end of the arc of `a` to the start of the arc of `b`, as `GapHoldsCorner a b`
    does.
  - `RespectsSections` rules out a cut strictly inside a target arc. So the parts of the corner
    covered by the two arcs hold no extra corner.

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
- **C4.** Proved by leavitt-units: `cornerTwoGonInput` (90245333d) and `osinCornerTwoGonSection`
  (0c42391c2), with the statement of d0a41c1da unchanged.
- **C5.** Proved by hs-vanishes: `cellFaceCountInput` (a6a2cadda), with the statement of
  bdd687708 unchanged.
- **C6′.** `TwoGonHoldsInput`, stated here in the vocabulary of C4 and C5. debt-conditional
  proves it.
- **C6.** `EmptyTwoGonInput`, proved by fff-periodic.
- **Assembly.** `phiPrimeCountInput_of_smallFaces` (4beca2743). At section level,
  `osinPhiPrimeCountSection_of_pieces` (6401c70a6) proves `OsinPhiPrimeCountSectionStatement` from
  `OsinCornerTwoGonSectionStatement` and `OsinTwoGonHoldsSectionStatement`.

## R2: the inner region of a noncrossing pocket walk

Lead's item (09-13). Under R2 the inner `IsDiscRegion` of a pocket comes from
`BoundaryCycle.toDiscRegion_of_euler` (`SurgeryReclosedConnected.lean:106`), which needs χ of the
reclosed map of `sideFaces M w` along a noncrossing closed walk (`IsNoncrossingClosedWalk`,
26a7858f2) to equal χ of `M`. dgo-analytic handed the lemma over. Lead ruling: "hull-euler builds
`NoncrossingClosedWalkEuler`: `IsNoncrossingClosedWalk.reclosed_euler`, with outer following as a
hypothesis, model-tested on the rose."

Module `GroupApproximation/GGT/VanKampen/NoncrossingClosedWalkEuler.lean` (7e254eb66, fix
19866c7d6, green 0913-150114-7274, unwired). It imports `NoncrossingClosedWalkSides`,
`SurgeryReclosedConnected`, `PermFirstReturnOrbits` and `CactusTopology`, and no `Estimating/`
module. dgo-analytic's builder `PocketRegion.ofNoncrossingClosedWalk hw hout hfollows heuler`
(`Estimating/OsinPocketRegionNoncrossingWalk.lean`) takes `heuler` of exactly this type.

- `innerVertexClass hw hM : KeptDart M (sideFaces M w) → InnerVertexIndex M w` sends a retained
  dart to the first reversed walk dart met by old rotation, or to its old vertex if there is none.
  `InnerVertexIndex M w` is the old vertices with no retained outer dart, plus the walk darts.
- `innerVertexClass_sigma` (uses `hout`), `innerVertexClass_rep`, `innerVertexRep_sameCycle` feed
  `OrbitClassifier.orbitEquiv`. So `inner_vertexCount`.
- `vertexCount_add`, `edgeCount_add`, `faceCount_add`: the two reclosings together have `|w|` more
  vertices, `|w|` more edges and two more faces than `M`.
- `reclosed_euler` from these and `reclosedMap_euler_preserved` on the outer cycle.
- `innerDiscRegion hw hM hout : IsDiscRegion M (sideFaces M w)`.
- `OsinPocketPinchedTwoGonOuterFollows.pinchCycle_outerCycle_followsBoundary` is a landed model
  where outer following holds and inner following fails, so `hout` is the right strength.

- The existing `reclosedMap_euler_preserved` (`SurgeryReclosedPlanarity.lean:28`) needs
  `boundary.FollowsBoundary`. Under R2 only the outer cycle follows.
- The unconditional form is false. Hand model test: one vertex and three loops, darts 0..5,
  `alpha = (0 1)(2 3)(4 5)`, `sigma` 1→0→3→2→5→4→1, so `χ = 1 − 3 + 4 = 2`.
  `w = [0,2,4]` satisfies every field of `IsNoncrossingClosedWalk`, since `sigma (alpha d) = d`
  for `d ∈ w`, and `sideFaces` is the three monogons. The reclosed rotation is the 6-cycle
  0→3→4→1→2→5→0, so the reclosed map has 1 vertex, 3 edges, 2 faces and `χ = 0`.
- The walk is a three-petal rose, and every pair of passages crosses. `turn_mem` forces only the
  alternation of reversed and forward walk darts, which excludes a crossing only at a vertex
  passed twice. kh-ejz has the docstring caveat.
- With `(hw.outerCycle hM).FollowsBoundary` it holds. At a walk vertex, outer follows means that
  the first walk dart after each departure `f_i` is the arrival `r_i` of the same passage.
  - The inner reclosed rotation sends `r_i` to `f_i` and agrees with `sigma` on outside sectors,
    so each passage is one vertex: `V(N_in) = V_outsideOnly + w.length`.
  - `reclosedMap_vertexCount` on the outer cycle gives `V(N_out) = V_insideOnly + V_walk`.
  - The kept darts of the two sides overlap exactly in the walk-edge darts, so
    `E(N_in) + E(N_out) = E + w.length`.
  - `reclosedMap_faceCount` on both sides gives `F(N_in) + F(N_out) = F + 2`.
  - So `χ(N_in) + χ(N_out) = χ(M) + 2`, and `reclosedMap_euler_preserved` gives
    `χ(N_out) = χ(M)`.
- Candidate form, sent to dgo-analytic:

```lean
theorem IsNoncrossingClosedWalk.reclosed_euler (hw : IsNoncrossingClosedWalk M w)
    (hM : M.IsPlanar) (hout : (hw.outerCycle hM).FollowsBoundary) :
    (reclosedMap M (sideFaces M w) (hw.innerCycle hM)).eulerCharacteristic =
      M.eulerCharacteristic
```

The lemma is needed under R2, and also under R1 for configuration A (dgo-analytic's correction,
09-13). sec2-sentences' `exists_kept_of_pocketRegion` (`Estimating/OsinPocketKeptCell.lean:100`)
takes `P : PocketRegion S.diagram` and `hinner : P.inner.cycle = K.walk`, with no
`FollowsBoundary`. So the kept cell of a pinched pocket walk whose outer cycle follows is
`exists_kept_of_pocketRegion … (ofNoncrossingClosedWalk hw hout hfollows
(hw.reclosed_euler _ hfollows)) rfl havoid`. The lead still prefers R2: under R1, configuration A
has no planned proof. hull-select produces the four inputs of `ofNoncrossingClosedWalk` for
non-simple pocket walks and consumes `reclosed_euler`; it has the statement and SHAs.

## Census

No rows yet. The rows wait for the closure of `PhiPrimeCountInput`, which carries the Euler count
inside the proof of `thm:hull` (tex 1636, through Osin's Lemma 9.7(a)). The section assembly
6401c70a6 is conditional and adds no row. With C4 proved, one binder remains.

## Next

1. When debt-conditional lands a producer of `OsinTwoGonHoldsSectionStatement` (or of
   `TwoGonHoldsInput`), verify the landing:
   - ancestor of origin/main;
   - md5 of the green record equal to the landed file;
   - statement unchanged;
   - no `sorry`, `axiom` or `native_decide`.
2. Then write the closure
   `osinPhiPrimeCountSection := osinPhiPrimeCountSection_of_pieces osinCornerTwoGonSection hT`
   in a module importing both producers, with `#audit_closed_axioms`, probe and land it.
3. Then the census rows.
4. The R2 Euler lemma is green. A consumer fills `heuler` of `PocketRegion.ofNoncrossingClosedWalk`
   with `hw.reclosed_euler Delta.planar hfollows`. Wiring `NoncrossingClosedWalkEuler` is the
   lead's call.
