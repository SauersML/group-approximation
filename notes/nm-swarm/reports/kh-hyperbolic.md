# kh-hyperbolic — `IsHyperbolicGroup (GHB 7)` for the Kotowski–Ollivier lattice route (relaunch 2026-09-12)

Lane clone thm-d. The leaf served is `hhyp : Hyperbolic.IsHyperbolicGroup (GHB 7)` of
`ghb7LatticeRouteInput hconj h3 h4 hhyp hT` (Kazhdan/GHBLatticeRoute) and of kh-ejz's
`GHBQuotient.kotowskiOllivierStatement_of_ghb7ConjHyp hconj hhyp` (Kazhdan/GHBLatticeRouteKazhdan,
8085b58cd).

## CHAIN
- Stokes ladder (Kazhdan/GHBHyperbolicStokesLadder, green 0912-002938, 0f5344b90):
  `ChainFillingBound Adj Tri A` with coset data `mem, ℓ, M₀, vert` gives `LinearStokes S K`
  (`linearStokes_of_chainFillingBound`), and that gives `IsHyperbolicGroup` (`isHyperbolicGroup_of_linearStokes`).
- H5 glue (Kazhdan/GHBHyperbolic): `ghbLetters`, `finite_vertexGroup`, `exists_wordNorm_le_vertexGroup`,
  `cosetSection`, `wordDist_cosetSection_le`, `letterVertex`, `rep_letterVertex`,
  `linearStokes_ghb7_of_chainFillingBound`,
  `isHyperbolicGroup_ghb7_of_chainFillingBound (hfill : ChainFillingBound CCKW.cosetComplex.G.Adj CCKW.cosetComplex.Tri 6) : Hyperbolic.IsHyperbolicGroup (GHB 7)`.
- HC10–12 (Kazhdan/GHBHyperbolicFilling, imports SystolicDisc only): `TypedCountStatement X n`, `BoundarySumStatement X`,
  `faceDegree_outer_eq`, `chainFillingBound_of_leastDiscs hfill hfold hL hcount hsum : ChainFillingBound X.G.Adj X.Tri 6`,
  `CCKW.chainFillingBound_cosetComplex hfill hfold hcount hsum`,
  `GHBQuotient.isHyperbolicGroup_ghb7_of_discInputs (hfill : Systolic.FillingStatement CCKW.cosetComplex) hfold hcount hsum`.
- HC11 and HC12 discharged, and filling from simple connectivity (Kazhdan/GHBHyperbolicDiscCounts):
  `typedCountStatement_of_typed τ hτ`, `boundarySumStatement X`, `CCKW.typedCountStatement_cosetComplex`,
  `GHBQuotient.isHyperbolicGroup_ghb7_of_zipFold (hzip : Systolic.ZipSpurStatement CCKW.cosetComplex) (hfold : Systolic.MirrorFoldStatement CCKW.cosetComplex) : Hyperbolic.IsHyperbolicGroup (GHB 7)`.
  The lead asked for this signature to stay stable.
- Open leaves, as assigned by the lead on 09-12 (hzip reassigned from kh-ejz):
  - `Systolic.ZipSpurStatement`: kh-torsion, `Systolic.zipSpurStatement X` in GGT/SystolicDiscZip.lean.
  - `Systolic.MirrorFoldStatement`: fff-periodic, `Systolic.mirrorFold X` in GGT/SystolicDiscMirrorFold.lean.

## LANDED (09-12)
- 0ac9f4538 (unverified): GHBHyperbolic, adopted from the shared tree (this lane's target path; no other lane
  listed it), and GHBHyperbolicFilling.
- b049d3faf (unverified): GHBHyperbolicDiscCounts.
- Probe 0912-094206-48022 (base 88688fc8d): GHBHyperbolic BUILT; the bytes on main match green record 578cd331.
  GHBHyperbolicFilling and GHBHyperbolicDiscCounts were not reached: go-sr1's GGT/SystolicDiscFilling and
  GGT/SystolicDiscCounts are red on main. The errors are forwarded to go-sr1.
- 3e6d8448a: this report.
- 6827a8024 (unverified): decoupling. Filling takes `hfill` and imports SystolicDisc only. The discharge from simple
  connectivity moves into zipFold in DiscCounts. Rule 22 grep: neither changed declaration has another user.
- 67efd4db8 (unverified): `List.length_nil` in place of the unused `List.length_singleton` in
  `faceDegree_outer_eq`. Probe 0912-094958-2788 had failed on the omega goal there.
- Probe 0912-095158-18076 (base 67efd4db8): GHBHyperbolicFilling PROBE GREEN. All four declarations pass
  `#audit_axioms`; the bytes on main are the probed bytes.

## EARLIER LANDINGS (09-11/12)
f2d8712cd KMSGroupPresentation; 8e9bd8324 UnipotentSylowCounts with KazhdanHypSymLocalData; a49d59853
KazhdanHypSymPowerDisc; 7c06a251d VanKampen/TypedTriangularDiscCounts; 06fa3aa1f GHBHyperbolicStokesPolygon;
0eb80e334, 0f5344b90 GHBHyperbolicStokesLadder; f1505ea1e, 81cc287f4 KazhdanHypGirthEight bridge and from-filling;
888400dcc, b2c9d8f50 KazhdanHypGirthEightSpurCountermodel and KazhdanHypSharpExistenceResiduals.

## NEXT
- Re-probe DiscCounts when go-sr1's fixes land, and land normally when green.
- When `Systolic.zipSpurStatement` (kh-torsion) and `Systolic.mirrorFold` (fff-periodic) land:
  `isHyperbolicGroup_ghb7 : Hyperbolic.IsHyperbolicGroup (GHB 7) := isHyperbolicGroup_ghb7_of_zipFold (zipSpurStatement _) (mirrorFold _)`,
  with the names adjusted to what lands.
- Wiring: GHBHyperbolic, Filling and DiscCounts join a later root-wiring wave once green, per the lead. The
  Ladder and TypedTriangularDiscCounts are in the current wave, so edits to them or to their imports land NM_ATTIC
  until a probe is green.

## TRAPS
- The nmland import guard holds even with NM_UNVERIFIED: land a module and its unlanded imports in one call.
- `hτ` and `htri` of SystolicDiscCounts take implicit `{x y z}`, while the named Props take them explicitly
  (`fun h => htri _ _ _ h`).
