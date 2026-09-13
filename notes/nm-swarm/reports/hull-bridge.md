# hull-bridge lane report

## Scope
Hull 7.1 LEAF 3 (Osin Lemma 5.1): produce `RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement`,
and Gromov's theorem (linear isoperimetric inequality over bounded relators gives a hyperbolic group).

## Compiled on main
- Refutations: `not_relativeDehnTransferStatement` (GGT/HullSCLemma44DehnTransferRefutation).
- Lemma 5.1 area induction at least-area certificates (GGT/HullSCLemma51QuasiGeodesicTransfer).
- Embedded bridge, bounded bridges, least-area family bridge (GGT/HullSCLemma51EmbeddedBridge,
  HullSCLemma44BoundedBridge, HullSCLemma44BoundedFamilyBridge, HullSCLemma44BoundedLeastAreaFamilyBridge).
- Gromov's theorem: Algebra/DiscreteStokes … BowditchSlim, LinearIsoperimetricHyperbolic
  (`DiscreteStokes.isHyperbolicGroup_presentedGroup_of_linearIsoperimetric`).
- Hyperbolic ⇒ linear Stokes (Algebra/HyperbolicLinearStokes); quotient Stokes (Algebra/QuotientLinearStokes).
- Clause (a) for the quotient family (GGT/HullSCLemma51QuotientStokes) and
  `relativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement_of_letterPullback` (GGT/HullSCLemma51EmbeddedProducer).
- `HullSCRelativeLeastAreaDiagram` red fix (sec5's module, by lead decision).

## Open leaf
`QuotientPeripheralLetterPullbackStatement` (clause (b), DGO 4.24 ⇐ in letter-pullback form).
Route approved: nonplanar induction on the quotient ball radius, one Osin move per step
(M1: shorten any non-geodesic cyclic subword; M2: certificate cut), face relations at cosets,
induction hypothesis on quotient-ball stretches.

## Compiled for the letter pullback
- GGT/HullSCLemma51LetterWords (inverse respelling, one peripheral letter per coset in a geodesic).
- GGT/HullSCLemma51FaceRelation (bounded products, coset letters, face relations, face_relation_split).
- GGT/HullSCLemma51LetterMoves (shortcut, certificate cut with geodesic sides, cross-coset exclusion).
- The induction (D), GGT/HullSCLemma51LetterPullback, belongs to hull-component.

## Relaunch 2026-09-12
- (B) FaceRelation and (C) LetterMoves compiled in probe 0912-003729 (GREEN) at exactly the bytes on main.
  They are not yet wired into the root; the lead wires in waves.
- hull-component (D): LetterPullbackAtoms and Close compiled. Rotate was red on two proof slips; the fix
  landed unverified and is being re-probed. (D) needs nothing more from (B) or (C).
- Next: the endpoint module GGT/HullSCLemma51EmbeddedBridgeHolds,
  `relativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement_holds :
  RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{u, v, w}`, from
  `relativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement_of_letterPullback` and (D)'s producer of
  `QuotientPeripheralLetterPullbackStatement`. It will land when (D)'s module is on main.

## Swarm 2026-09-13
- Landed: GGT/HullSCLemma51LetterPullbackCutLift (dfa2dfb11), green in probe 0913-041834-85289.
  `CutLift` records one certificate cut of a rotated lift; `CutLiftOutcome` is the interface between
  the cut move and its outcomes.
- Peers on the chain (all on main):
  - debt-conditional: GGT/HullSCLemma51LetterPullbackCut (457c543a8, probe 0913-044157-34176 green),
    `letterStepBound_of_cutLiftOutcome` (the M2 move bound from `CutLiftOutcome`).
  - hull-component: GGT/HullSCLemma51LetterPullbackCutOutcome (a1f2e52da), CutOutcomeSides
    (27f56e14b) and CutOutcomeRight (47b7225af), ending in `CutMove.outcome`: every cut move
    gives a pullback outcome.
- Closing modules:
  - GGT/HullSCLemma51LetterPullbackHolds: `CutLift.toCutMove`, `cutLiftOutcome` (through
    `CutMove.outcome`), and
    `quotientPeripheralLetterPullbackStatement_holds : QuotientPeripheralLetterPullbackStatement.{u, v, w}`.
  - GGT/HullSCLemma51EmbeddedBridgeHolds: `relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed :
    RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}`.
- LANDED 18682110d, green in probe 0913-050027-71372 (both endpoints `#audit_closed_axioms`), queued
  for wiring. `QuotientPeripheralLetterPullbackStatement` and
  `RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}` are closed; hbridge has no
  residual Props.
- Next: the next roster item for this lane.

## Flips over the Greendlinger waist 2026-09-13
- The conditional baseline had 74 findings on the bridge binder. Each consumer now has a form
  that applies `relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed` and keeps
  `hgreendlinger` (`GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}`)
  as its only binder. Each form applies every closed producer at once. The lead split the flips
  by consumer module; when a declaration fits two sets, the module's owner wins:
  - hull-bridge, GGT/HullSCGreendlingerForms: the general canonical quotient, one step, tower and
    ball form, the torsion-free canonical quotient and one step, and the bounded canonical
    Lemma 4.4.
  - hull-bridge, Manuscript/NonMF/TorsionFreeGreendlingerSentences: both general hull-paragraph
    sentences, the hull theorem at Osin's notion over a torsion-free group, the three
    saturation and theorem sentences, and the Hull citation sentence.
  - hull-bridge, Manuscript/NonMF/TorsionFreeGreendlingerForms (17 forms): the printed
    `sec:torsion-free` endpoints at the current, Osin and limit-set notions (thm:hull,
    lem:saturation, thm:torsion-free, cor:regular-nonmf-algebra), the Proposition 2.3 quotient
    field, Hull Corollary 7.4, the literature inputs and the Fournier-Facio paragraph. They apply
    `kotowskiOllivier_closed`, `finitelyPresentedInfiniteSimple_closed`, the Osin 1.1 producer
    and the closed DGO/GO forms.
  - fff-periodic: TorsionFreeFourLeaves, SectionSentencesFourLeaves, `TheoremC.manuscriptTorsionFree*`
    and the other KO and MirrorFold binders. ghw-assembly: the Kazhdan, CCKW and Hyde-Lodha
    consumers. theoremc-retire: TheoremCAssemblyGreendlingerLeaf (c5f953323), both forms of
    Theorem C.
- LANDED 2aa98f8cc, green in probe 0913-071409-41646 (both modules BUILT, `#audit_axioms`):
  HullSCGreendlingerForms and TorsionFreeGreendlingerSentences. Census rows for tex lines 1636,
  1644, 1662, 1665, 1680 and 1698.
- LANDED 99db3338a, green in probe 0913-081212-8538 (base 296b0173f, both modules BUILT,
  `#audit_axioms`): TorsionFreeGreendlingerForms and the bounded Lemma 4.4 form. Census rows for
  tex lines 1636, 1650, 1675, 284 and 1718. Both modules are queued for wiring and have no importers.
- The census lane has the old-to-new names for the 54 remaining baseline lines of this set
  (27 declarations, open-predicate and buried-conditional each).
- Residual Prop: `RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}` (W1) alone.
  When W1 closes, each final flip is one application.

## Collar steps 2026-09-13
- Next item from the lead: help kh-torsion with the collar steps of W1 (a). The step is
  `GeodesicCollarStatement` (GGT/VanKampen/SurgeryGeodesicCollar, 7bb586a06), applied to one
  side of the pocket and then, after `PocketRegion.withOuter` restarts the complement cycle, to
  the other side.
- kh-torsion's sub-piece, GGT/VanKampen/Estimating/OsinPocketRegionVertexSimple: LANDED 87715ad6e,
  green in probe 0913-091940-39141 (base 0793191e3, BUILT, `#audit_axioms` on all ten
  declarations). Suppose both cycles of a pocket region follow their boundary walks. Then
  `PocketRegion.isSimpleClosedWalk_inner_cycle` shows the pocket's cycle is a simple closed walk,
  and `PocketRegion.isSimpleClosedWalk_invDarts_outer` shows the same for the inverse of the
  complement's cycle.
  - The general step is `BoundaryCycle.eq_of_vertexOf_eq_of_complement`: around a vertex, the
    two boundary walks together cover its whole rotation orbit.
  - The module also adds `IsSimpleClosedWalk.of_next`, `vertexOf_alpha_eq_next` and `rotate`.
  - Queued for wiring. It has no importers, and it is infrastructure, so it has no census row.
- The collar insertion uses it as follows: the collared side is a sub-path of this walk, and its
  endpoints differ exactly when the rest of the walk is nonempty.
- kh-torsion's second sub-piece, the disc-level corner join (the inverse of `PinchSplit`):
  - GGT/VanKampen/SurgeryCornerJoinMap: LANDED e7fa1c6ab, green in probe 0913-105542-93925
    (BUILT, `#audit_axioms`). `CornerJoin.toCombMap` is `VertexJoin.toCombMap`. A face cycle
    `alpha x :: xs ++ alpha y :: ys` (`Cycle`) splits into the faces `alpha x :: ys` and
    `alpha y :: xs`, and every other face keeps its enumeration. `sameCycle_mul_swap_iff` gives
    the vertices of the join.
  - GGT/VanKampen/SurgeryCornerJoinDiagram: LANDED 336c80ccc, green in probe 0913-111152-20791
    (BUILT, `#audit_axioms`). `CornerJoin.Input.diagram` is O-equivalent to the old diagram with
    the same cells (`cellMap`, `cellDarts_eq`, `outerDarts_eq`). It has the walks
    `faceBoundary_left_darts`, `faceBoundary_right_darts` and `faceBoundary_kept_darts`, one face
    more and one vertex fewer. The input carries the value of the left half, and `right_value`
    derives the other half.
  - Both are queued for wiring. They are infrastructure, so they have no census rows.
- kh-torsion's third sub-piece, GGT/VanKampen/SurgeryGeodesicCollarJoin: LANDED ce39bca65, green
  in probe 0913-132438-5905 (base 746028b24, BUILT, `#audit_closed_axioms` on
  `GeodesicCollar.joinStatement`, `#audit_axioms` on nine lemmas). It proves kh-torsion's
  `JoinStatement`, the join stage of the collar insertion.
  - A strip `p ++ q` along a side `p` of value one, with a nonempty rest `r`, is joined across by
    the corner join of `alpha` of the last dart of `q` and `alpha` of the last dart of `p`
    (`Strip.joinInput`). The strip face splits into a face enumerated by `q` and a face
    enumerated by `p`.
  - The join makes the head vertices of `p` and `r` one vertex, so `r` is a simple closed walk of
    the join (`Strip.join_walk`). The face of `q` replaces the strip face in the face set, which
    cuts `p` off, so the boundary darts are the darts of `r` (`Strip.join_boundary`).
  - The transport is the identity on darts (`Strip.joinTransport`).
  - Queued for wiring. It is infrastructure, so it has no census row.
- kh-torsion's fourth sub-piece, GGT/VanKampen/SurgeryGeodesicCollarInsert: LANDED 2750beb3d, green
  in probe 0913-152308-19611 (base ae463a301, BUILT, `#audit_closed_axioms` on
  `GeodesicCollar.insertStatement`, `#audit_axioms` on eight lemmas). It proves kh-torsion's
  `InsertStatement`, the insertion stage of the collar surgery.
  - The strip face `F` of `p ++ q` is enumerated from the head of `p`, so `p` is the prefix up to
    the head of `q` (`FaceBoundary.isFaceCycle.exists_rotate_eq`,
    `CornerInsertion.exists_forwardOffset_eq`). `GFaceWordInsertion.exists_split_corner_output`
    then inserts a path reading `g` from the head of `p` to the head of `q`.
  - The new face set is `insert suffixSide (S.erase F)` (`Strip.insertFaces`). Its boundary darts
    are the path followed by the image of `r` (`Strip.insert_boundary`), and together they form a
    simple closed walk (`Strip.insert_walk`). The transport is `originalEmbedding` with
    `originalCellMap` (`Strip.insertTransport`).
  - The first probe (0913-150935-4440) failed on two deprecated `List` names and a
    `rw [List.map_map]` that the rebased dart types blocked. The proof of that step now uses
    `Eq.trans`.
  - Queued for wiring. It is infrastructure, so it has no census row.
- Next item from the lead: a StripStatement sub-module (Double or Pinch) from kh-torsion, written
  in a new module of this lane and stated over the weakest hypothesis its step needs. I have asked
  kh-torsion which one to take.

## Risks recorded
- `BoundedRelativeLinearAreaTransferStatement` may be unprovable: its W-only area predicate cannot see the
  relations of G (docstring in GGT/HullSCLemma44BoundedInput). Nothing routes through it.
- `peripheralPullback` clause of `RelativeIsoperimetricControl` is false (prose counterexample in the
  EmbeddedBridge header).
