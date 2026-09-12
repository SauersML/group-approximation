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

## Risks recorded
- `BoundedRelativeLinearAreaTransferStatement` may be unprovable: its W-only area predicate cannot see the
  relations of G (docstring in GGT/HullSCLemma44BoundedInput). Nothing routes through it.
- `peripheralPullback` clause of `RelativeIsoperimetricControl` is false (prose counterexample in the
  EmbeddedBridge header).
