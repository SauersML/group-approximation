# ghw-charp2 lane report

## Item 7 (09-13): the LoopCut site census (read-only; gates ruling (A))

Lead order: list every site that builds a `RealizedSectionFamily` or uses `weight_maximal`, `card_minimal` or
`RespectsSections`, on origin and in drafts.  At each site, say whether the new region satisfies `target ≠ some source`.
Prepare the patches in the lane backup, and flag the sites where the new region can be forced to run from a cell to
itself.

The form tested is patch 01: `RespectsSections cuts a := a.2.target ≠ some a.2.source ∧ (a.2.target = none → ∃ j,
TargetsSectionIndex cuts j a)`.  audit-sec5's exact form had not arrived.

### Status: census DONE, refreshed at origin 35866daf3 with the drafts on disk re-read; no Lean edit landed, no probe

### Construction sites

| # | Site | Owner | New region | `target ≠ some source` |
|---|---|---|---|---|
| 1 | `Estimating/OsinAppendixCutMerge.lean` `false_of_cons_singleton` l.62, `false_of_collapse_singleton` l.125 | hl-lemma46 | merged face (caller hypothesis); retained regions | holds: caller hypothesis; retained by the index bijection |
| 2 | `Estimating/OsinPocketZeroCellMerge.lean` `mergedGeometry` l.221 | hull-select | merged face | holds iff the original arcs join distinct cells or a section; planned callers do |
| 3 | `Estimating/OsinUnboundCaseOne.lean` `false_of_quadrilateral_region` l.102 | hull-unbound | face `Q` | **same-cell forceable**: `source`, `target` unconstrained (cap after a G-region collapse) |
| 4 | `Estimating/OsinUnboundSharedEdge.lean` `false_of_digon_toward_cell` l.377 | hull-unbound | digon `i → some i₂` | **same-cell forceable** at `i₂ = i` (an edge with cell `i` on both sides) |
| 5 | same file, `false_of_digon_toward_outer` l.421 | hull-unbound | digon, target none | holds: target none |
| 6 | `SurgeryGFaceMergeRegions.lean` `transportSection` l.536 | NONE | retained only | holds: bijection (user `OsinUnboundMerged` automatic) |
| 7 | `SurgeryPinchSplitSections.lean` `transportSection` l.198 | fff-periodic | retained only | holds: bijection (user `SurgeryPinchSplitExtremal` automatic) |
| 8 | `Estimating/OsinAppendixDescentCut.lean` l.222; `Estimating/OsinAppendixSectionBridge.lean` l.95, l.166 | dgo-analytic; hull-select | empty family | holds: vacuous |
| 9 | `Estimating/OsinPocketDiscMerge.lean` `false_of_disc_collapse_singleton` l.196 (2aa17abb0) | fff-periodic | merged disc face (caller hypothesis); retained | holds: caller hypothesis; bijection |
| 10 | `Estimating/OsinPocketDiscEmptyTwoGon.lean` `emptyTwoGonInput_holds` l.33 (2aa17abb0) | fff-periodic | merged face, cell `i` to section `j` | holds: target none |
| 11 | `Estimating/OsinUnboundCaseOneFace.lean` `false_of_quadrilateral_face` l.379 (7f7ba2b4f) | theoremc-retire | face `Q` on an unselected face | **same-cell forceable**: the cap on the face (the loop iff is already recorded) |
| 12 | `Estimating/OsinUnboundCaseOneRun.lean` `osinLemma94CaseOne_false_of_walk` l.35, `osinLemma94CaseOneInput_of_walk` l.78 (3292f7a20; `S.weight_maximal` l.69) | theoremc-retire | as 11, from the face walk | **same-cell forceable**, inherited: both sides of the connector pair on one cell |
| 13 | `LoopCutCapCounterexample.lean` (0c7a92957; `capSectionFamily` l.396, `weight_maximal` l.569, `not_loopCutInput` l.586) | audit-sec5 | the cap from `Π` to `Π` | fails by design; its docstring (l.40) says it retires under (A) |
| 14 | `Estimating/OsinLemma94InsertionTransport.lean` `insertionSection` l.264 (c652fa749) | sec2-sentences | retained only | holds: bijection (`insertionTransport` automatic) |
| 15 | `Estimating/DiscEmbeddingAwayUnbound.lean` `retainedSection` l.153 (ff8e8fce9; l.36 in the unlanded disk rewrite) | simple-group | retained only | holds: bijection (`retainedDistinguished` automatic) |
| 16 | `SurgerySpikeDeletionRegions.lean` `transportSection` l.484 (0838416d4) | sec5-sentences | retained only | holds: bijection (`OsinLemma94SpikeTransport.lean` `transportDistinguished`, ba4233ef8, automatic) |
| 17 | `Estimating/OsinPocketZeroCellMergeFalse.lean` `false_of_disc_pair_singleton` l.52, `false_of_zeroCellPocket` l.81, `ZeroCellPocketMergeStatement` l.136 (ce1028aa1) | hull-select | merged pocket face | **same-cell forceable** at statement level: `source` and `target` are free |
| 18 | `Estimating/OsinLemma94PolygonCovers.lean` `alpha_faceOf_not_cell_of_unbound` l.95 (2b2e16cc6; `S.weight_maximal` l.105, l.107) | hull-count94 | the digon of row 4 | **same-cell forceable**, inherited from row 4 at `j = i`; feeds the closed `osinLemma94PolygonCoversInput` |

Rows 9-12 landed after the 08:47 file list, and rows 14-18 appeared after 09:15.  For row 12, the walk
(`OsinLemma94CaseOneWalk.lean:42`) gives `kind C.source = .cell source` and `target = some j → kind C.target = .cell j`.
On origin theoremc-retire already routes the same-kind pairs through the named hypothesis
`OsinLemma94CaseOneSameCellStatement` (`OsinUnboundCaseOneFace.lean:466`), in `osinLemma94CaseOneInput_of_walk_of_sameCell`
(l.89).  Only the unconditional `osinLemma94CaseOneInput_of_walk` rests on the cap.

### Use sites

- `T.respects` applied to `target = none`: `OsinAppendixAssemblyDescent.lean:199` (dgo-analytic) and
  `OsinAppendixAssemblyPocket.lean:212` (NONE) need `.2`.
- `weight_maximal` and `card_minimal`:
  - `OsinLemma94PlanarPieces.lean:149-153` (hull-unbound) is unchanged;
  - `OsinUnboundCaseOneRun.lean:69` is row 12, and `OsinLemma94PolygonCovers.lean:105, 107` is row 18;
  - `OsinLemma94SpikeTransport.lean:44-50` (sec5-sentences) carries them over automatically, and
    `OsinLemma94PendantRemoval.lean:173` (jacobson) reuses that transport.
- `respectsSections_of_sameTargetProfile` gains `hloop` (Rule 22).  Its ten users are CutMerge:147, DiscMerge:218,
  CaseOne:159, CaseOneFace:433, SharedEdge:342, GFaceMergeRegions:547, PinchSplitSections:209, InsertionTransport:277,
  DiscEmbeddingAwayUnbound:167 and SurgerySpikeDeletionRegions:495, all patched.
- New lemmas:
  - `regionFamily_noLoop` for InnerGRegion, InnerDiscRegion, FaceEdgeDoubling, DiscEmbeddingAway, GFaceMerge,
    PinchSplit and SpikeDeletion;
  - `mergedGeometry_loop_iff` for ZeroCellMerge and DiscMerge.
- `NoLoops` and `LoopCutInput` (`OsinAppendixSectionInduction.lean:43, 86`, used at l.174-182): patch 07 keeps both
  Props and every `hloop` binder.  It adds the closed producers `GloballyDistinguishedSectionFamily.noLoops`,
  `loopCutInput` and `osinLoopCutSection`.
- Unaffected:
  - these take `S` as a parameter only:
    - `OsinLemma94RegionSideCount.lean` (audit-intro);
    - `OsinPocketSectionFaceSet.lean` (kh-ejz);
    - `OsinLemma94CaseOneWalkHolds.lean` and `OsinLemma94CaseOneWalkLists.lean` (ko-closed);
    - `OsinLemma94PolygonRealization.lean` (hull-unbound);
    - `OsinAppendixEulerCornerTwoGon.lean` (leavitt-units);
  - `OsinPocketPinchedTwoGonModel.lean` (dgo-geometric) builds no family;
  - the eight VanKampen modules changed between c0181d92f and ccd23ffee use none of the census tokens;
  - of the four modules added by 35866daf3, `OsinLemma94CellArcs` (ko-closed), `OsinPocketMultipleEdgeTransport`
    (hl-lemma46) and `SurgeryCornerJoinMap` (hull-bridge) use none; `OsinLemma94CuttingChains` (hull-unbound, disk
    edit unlanded) takes a dart-minimal `S` as a parameter only;
  - `weight_maximal`/`card_minimal` of other selection structures (over `Finset`, `RealizedRegionFamily` or
    `RealizedGeometricFamily`, no `RespectsSections`), a token collision: `Selection`, `RegionGlobalSelection`,
    `RegionLegalSelection`, `GeometricGlobalSelection`, `GeometricLegalSelection`, `GFaceCornerLegalSelection`,
    `GFaceCornerRegionSelection`, `GFaceLegalSelectionInsertion`, `CandidateWeightCounterexample`,
    `GeometricSelectionModel`, `SelfContiguitySelectionModel` (all NONE);
  - docstring mentions only: `OsinAppendixEulerCount:51` (NONE), `OsinAppendixEulerEmptyTwoGon:24` (hull-euler),
    `SingletonFaceRegion:26` (hull-unbound), `UnboundScaledDecomposition:39-40` (NONE);
  - the sweep at 35866daf3 (files containing `RealizedSectionFamily`, `weight_maximal`, `card_minimal` or
    `RespectsSections`) lists the same 45 files on origin and on disk, and each is accounted for above;
  - these build no family either:
    - the `∃ T : RealizedSectionFamily` Props (`OsinAppendixSectionInduction.lean:70, 131, 154, 161`);
    - the `hb` binders (`OsinAppendixSectionMultipleEdge.lean:173, 260`);
    - `OsinAppendixDescentInduction.lean:261`, which reuses `S`;
  - the other selection structures are different structures.
- Not LoopCut, flagged: two modules declare the same lemmas.
  - `DiscEmbeddingAwayUnbound.lean` (simple-group, l.39-66) and `OsinLemma94InsertionTransport.lean`
    (sec2-sentences, l.49-76) both declare five `DiscEmbeddingAway.regionCandidate_*` lemmas, and five more under
    other names.
  - `OsinLemma94InsertionTransport` is now in the root (`GroupApproximation.lean:5023`), so wiring the origin version
    of `DiscEmbeddingAwayUnbound` (ff8e8fce9) fails with "already declared".
  - simple-group's unlanded rewrite on disk (10:25) drops those lemmas and imports `OsinLemma94InsertionTransport`,
    so the flag clears once it lands.

### Same-cell forceable sites (these decide (A) versus the fallback)

1. SharedEdge `false_of_digon_toward_cell` at `i₂ = i` (hull-unbound).  Its only consumer is site 5.
2. CaseOne `false_of_quadrilateral_region` at `target = some source` (hull-unbound).  It has no users.
3. CaseOneFace `false_of_quadrilateral_face` at `target = some source` (theoremc-retire).  Its only user is site 4.
4. CaseOneRun (theoremc-retire): on origin the same-kind pairs already form the named hypothesis
   `OsinLemma94CaseOneSameCellStatement`.
   - Under (A), `osinLemma94CaseOne_false_of_walk` takes `hkind`.
   - The unconditional `osinLemma94CaseOneInput_of_walk` goes.
   - `osinLemma94CaseOneInput_of_walk_of_sameCell` passes `hkind` on and otherwise stays the same (patch 10 (f)).
5. PolygonCovers `alpha_faceOf_not_cell_of_unbound` at `j = i` (hull-count94).
   - The closed `osinLemma94PolygonCoversInput` (`OsinLemma94PolygonCount.lean:53`) rests on it.
   - Under (A), no polygon side covers an unbound dart of cell `i` whose reverse also lies on cell `i`, because
     `exists_relatorSide_of_unbound` (l.157) needs `hcell` at every `j`.
   - Such darts need their own count or exclusion, or that Prop reopens.
   - I found no length argument that excludes them: the enclosed subdiagram can hold relator cells.
6. ZeroCellMergeFalse `ZeroCellPocketMergeStatement` (hull-select, ce1028aa1, no consumers): it gains the premise
   `target ≠ some source`.
   The planned 9.7(a)/(b) callers read it off `S.respects`.

Under (A) the region at sites 1-5 is no competitor, so those darts need another argument.

### Patches (lane backup `backup/ghw-charp2/loopcensus/`, not probed)

- 01: Sections.
- 02: CaseOne and GFaceQuadrilateralRegion.
- 03: SharedEdge and FaceEdgeDoubling.
- 04: the GFaceMerge and PinchSplit transports.
- 05: CutMerge and InnerGRegion.
- 06: the Assembly `.2`.
- 07: closed `noLoops`, `loopCutInput` and `osinLoopCutSection`.
- 08: the ZeroCellMerge loop iff.
- 09: DiscMerge, DiscEmptyTwoGon and CaseOneFace (anchors refreshed at ccd23ffee; its (f) is superseded by 10 (f)).
- 10: InsertionTransport, DiscEmbeddingAwayUnbound, SpikeDeletionRegions, PolygonCovers (statement only),
  ZeroCellMergeFalse and CaseOneRun.

### Residual (exact)

- The lead's ruling on (A), and audit-sec5's exact form of the loop conjunct.
- The one-line competitor answers from hull-unbound, theoremc-retire and sec5-sentences have not arrived.
- Under (A), two Props need their own argument:
  - the same-kind Case 1 pairs, `OsinLemma94CaseOneSameCellStatement`, already a named hypothesis;
  - the self-facing unbound darts at site 5, without which `osinLemma94PolygonCoversInput` reopens.

## Item 6 (09-13): the `hlinked` and `hV` producers for the exterior Euler count

Lead order: take the producers of the hypotheses `hlinked` and `hV` of `card_add_six_le_of_linkedO`,
in a new module of my own, after confirming with hull-euler.

Module `Estimating/OsinAppendixEulerExteriorLinked.lean` (probe 0913-061116-68489 green; the seven
`#audit_axioms` lines list only propext, Classical.choice and Quot.sound):
- `linkedComponentO E a₀` is the set of regions of `E` linked to `a₀` through shared ends.
  `linked_linkedComponentO E a₀` is `hlinked` for it.
- `endCellsO E` is the set of ends of the regions of `E`.  `sideCellO_mem_endCellsO` is `hV` for it.
- `sideCellO_ne_of_not_mem_linkedComponentO`: a region outside the component shares no end with it.
- `mem_linkedComponentO_of_sideCellO_eq_none`: all regions with an end at the outer vertex lie in one
  component.
- `ExtPhiData.mono`, and `card_add_six_le_linkedComponentO`: `|C| + 6 ≤ 3|endCellsO C| + t` on every
  component `C`.

### Status: LANDED (infrastructure for `thm:hull`; no endpoint Prop, no census row)

- cbca8029b: a normal landing on green record 0913-061116-68489 (md5 9d523724).  Queued
  `GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerExteriorLinked ghw-charp2 cbca8029b`.
- Overlap check before landing: on origin, only `OsinAppendixEulerExterior` and `OsinAppendixEulerExteriorCount` use
  `SharesEndO`.  In the working tree, hull-euler's unlanded `OsinAppendixEulerExteriorTwoGon` has local two-gon lemmas and
  none of these names.  hull-euler has the SHA and the names.

### Residual (exact)

- Summing the count over the components and producing `ExtPhiData` from a section family stay in
  hull-euler's assembly.
- `PhiPrimeCountInput` (Osin Lemma 9.3) stays open behind C3-C6 and the assembly.

## Item 5 (09-13): C2 of `PhiPrimeCountInput` (Osin Lemma 9.3)

Lead order: take C2, the count `m + 6 ≤ 3c + t` on the exterior map Φ'', in a new module of my own.  Ask
hull-euler for the Lean name first, and check the planar Euler layer on main.

Finding: C2 is already on main, landed by hull-euler, so I wrote no module.
- `Embedded.RegionCandidate.card_add_six_le_of_linkedO` (`Estimating/OsinAppendixEulerExteriorCount.lean`,
  050822843, green 0913-045049-59145 at the landed md5).  Given `P : ExtPhiData family E`, a finset `V`
  holding every side cell, `E.Nonempty`, and `hlinked : ∀ a ∈ E, ∀ b ∈ E, Relation.ReflTransGen (SharesEndO E) a b`,
  it proves `E.card + 6 ≤ 3 * V.card + #{f | faceDegree f < 6}` on `phiMapO family E`.
- The proof applies kh-ejz's `edgeBound_of_subdividedMultigraph` (`OsinAppendixEulerMultigraph`, 04240bd43)
  through `phiMapO_dartCount`, `phiMapO_vertexCount_le`, `phiMapO_connected` and `phiMapO_planar`.
- C1 is `phiSubdividedMultigraphO` (`Estimating/OsinAppendixEulerExterior.lean`, 4e27d4965, green
  0913-044600-43289).

### Residual (exact)

- Nothing on origin uses `card_add_six_le_of_linkedO` yet.  Nothing produces `hlinked` or `hV` for a
  `GloballyDistinguishedSectionFamily` either.  Both belong to hull-euler's assembly.
- No Lean written, no probe run.  I asked the lead for a replacement piece.

## Item 4 (09-13): Jacobson probe record and the GHW char-0 archimedean split

Lead order:
1. `JacobsonComplementarySentence` has no probe record or queue line, and jacobson is silent.  Probe it at the
   current base without editing it, queue it under ghw-charp2, and send the tag to root-wire.
2. Split the char-0 archimedean half directly with ghw-assembly.  `Kazhdan/GHWCharZero.lean` is ghw-assembly's
   unlanded work in progress: no edits and no parallel copy.  Take only a piece ghw-assembly names, in my own module.

### Jacobson record: DONE

- Probe 0913-040230-50292 at base 42d443298 named
  `GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonComplementarySentence`.  Result: PROBE GREEN, EXIT=0.
- The probe rebuilt 0 modules; lake found the trace up to date and used the cached olean.  The clone's source md5
  (89f64931) equals origin and the base.  Origin has not changed the module, `FullDefectRingEJZUnconditional` or
  `JacobsonFiniteMatrices` since the base.
- The module is on origin, not in the ghw-charp2 overlay, so the green record lists only ghw-charp2 files.
- Queued `GroupApproximation.Manuscript.OneSidedMFRadical.JacobsonComplementarySentence ghw-charp2 42d443298`, with a
  comment line above it giving the tag.  root-wire has the tag and the caveat.

### Archimedean split: bridge landed; ghw-assembly's call site needs no change

- Background: ghw-assembly's on-disk `Kazhdan/GHWCharZero.lean` (saved 03:52) expected the old shape at lines
  368--372.  I proposed the bridge below to fix that with a one-line call.  The lead then ordered: land the bridge
  now in my own module without waiting for ghw-assembly, land exactly the probed bytes, and send ghw-assembly the
  name.
- Landed 86635025c: `GHW.exists_intPoly_eq_pow_mul_minpoly_coeff d M N hM hn a h i`, appended to
  `Kazhdan/GHWCharZeroPlaces.lean`, which has been root-wired since ce699b9b8.  The change is additive: no existing
  statement changed, and the name is new on origin and on disk.
  - Setup: `B = ℤ[t_1..t_d]`, `L = Frac B`, `K/L` finite with `finrank L K = n`, and `M > 0`.
  - Claim: suppose every coefficient of `minpoly L (M^N a)` is `algebraMap G` for some `G ∈ ℤ[t]` of total degree at
    most `N·n`.  Then so is `M^(N·n)` times every coefficient of `minpoly L a`.
  - Proof:
    - `c_i(M^N a) = M^(N(deg − i)) c_i(a)`, by `IsIntegrallyClosed.minpoly_smul` and `coeff_scaleRoots`;
    - `deg − i ≤ n`;
    - the witness is `M^(N(n − (deg − i))) · G`;
    - the degree bound is `totalDegree_mul` with `totalDegree_C`.
- Compiled evidence: probe 0913-044256-36897 (base 27f56e14b) is PROBE GREEN.
  - `GHWCharZeroPlaces` and `IntegerPlacesMinpoly` are BUILT, with 0 warnings.
  - The bridge depends on `[propext, Classical.choice, Quot.sound]`.
  - The landed bytes are the green bytes (md5 cd60c1fc).
- Premise change: ghw-assembly landed `Kazhdan/GHWCharZero.lean` at add35a53a (04:20; unverified, unwired).
  - Its call site (lines 371--378) now passes the scaled elements `M^N x` to `finite_of_minpoly_coeff` through
    `Set.Finite.of_finite_image`.
  - `finite_of_minpoly_coeff` no longer carries the `M^(N n)` factor.
  - So the line-372 break is gone and the one-line replacement is obsolete.  I sent ghw-assembly the name, the SHA
    and the signature, and said that no change is needed.

## Item 3 (09-13): the additive non-archimedean places for GHWFinitelyGeneratedCharZero

Lead order: take the unstarted piece of the residual `GHWFinitelyGeneratedCharZero`, after settling the file name and
the interface lemma with ghw-assembly.  ghw-assembly had already landed the grid finiteness (`Algebra/IntegerGridFinite`,
3108f1cc7) and started the archimedean places.  It proposed the non-archimedean statement below for ghw-charp2, and I
accepted it verbatim.

### Status: CLOSED (interface lemma; this item has no endpoint Prop)

- Compiled evidence: probe 0913-033545-85262 (base a4c5b47db) is PROBE GREEN, with `GHWCharZeroPlaces` and
  `IntegerPlacesMinpoly` BUILT.  All four declarations depend on `[propext, Classical.choice, Quot.sound]`.  The
  landed bytes are the probed bytes.

- `GroupApproximation/Algebra/IntegerPlacesMinpoly.lean` (new): `IntegerPlacesMinpoly.exists_places_minpoly_coeff d K hM`.
  - Setup: `B = ℤ[t_1..t_d]`, `L = Frac B`, `K/L` finite (`K : Type`, `[CharZero K]`), and `M > 0`.
  - Claim: there are additive valuations `v : Fin r → AddValuation K (WithTop ℤ)` and uniformizers `π` with
    `v j (π j) = 1` with this property.  Suppose `M^k b` is integral over `B` for some `k` and `-N ≤ v j b` for every
    `j`.  Then every coefficient of `minpoly L (M^N b)` is `algebraMap G` for some `G ∈ ℤ[t]` of total degree at
    most `N·[K:L]`.
- `Kazhdan/GHWCharZeroPlaces.lean`, restated.  By rule 22, no declaration outside the file uses the old statements.
  - The place bound is sharpened to `w c_i ≤ exp (N·(deg − i))`, in `_le` and in `_le_family`.
  - `GHW.exists_places_minpoly_coeff` now says that the coefficients of `minpoly L (M^N a)` are integer polynomials of
    total degree at most `N·[K:L]`.  The old statement was about `M^(N·[K:L]) c_i(a)`.

### Route

- Scaling: `c_i(M^N a) = M^(N(deg−i)) c_i(a)` (`IsIntegrallyClosed.minpoly_smul`, `coeff_scaleRoots`).
- Valuation bounds:
  - at `p | M`, the sharp bound gives `v_p(c_i(M^N a)) ≤ exp(−N(deg−i))·exp(N(deg−i)) = 1`;
  - at the degree place, `c_i(M^N a) ≤ exp(N(deg−i)) ≤ exp(N·[K:L])`.
- Integrality: `M^k·M^N a` is integral, so the coefficients of `minpoly B` of it lie in `B` and equal
  `M^(k(deg'−i)) c_i(M^N a)`.  `exists_algebraMap_eq` then clears the `p | M` denominators.
- Additive form: `ValuationWithTopInt.addVal`, `addVal_eq_one` and `neg_le_addVal_iff`.  The case `b = 0` is trivial.

### Landed

- 0379bac08: `Algebra/IntegerPlacesMinpoly.lean` (new) and the restated `Kazhdan/GHWCharZeroPlaces.lean`.  This was a
  normal landing on the green record 0913-033545-85262.  ghw-assembly has the SHA and the signature.

### Census and wiring

- Row b6d1590be7ab now also cites `IntegerPlacesMinpoly.exists_places_minpoly_coeff`.  It stays `partial`, because the
  char-0 Prop is open.
- Queued `GroupApproximation.Algebra.IntegerPlacesMinpoly ghw-charp2 0379bac08`.  It imports `GHWCharZeroPlaces`,
  which imports `IntegerGaussValuations`.

### Residual (exact)

- None for this item.
- Still open, owned by ghw-assembly (the archimedean places over grid points, Noether normalization over ℚ, and the
  assembly through `hasHaagerupProperty_of_countable_places`; the grid finiteness `IntegerGridFinite` has landed):
  `GHWFinitelyGeneratedCharZero : ∀ (F : Type) [Field F] [CharZero F] (s : Set (GL (Fin 2) F)), s.Finite → HasHaagerupProperty.{0, 0} (Subgroup.closure s)`.

## Item 2 (09-13): places over ℚ(t_1..t_d) for GHW characteristic 0

Lead order: characteristic 0 belongs to ghw-assembly, which owns the grid/Nullstellensatz finiteness, the archimedean
places and the assembly.  ghw-charp2 builds the non-archimedean places over ℚ (the degree place, the places over
p | M, `exists_places_over`) on the char-p template.  Printed sentence: tex 1146--1147, the GHW Theorem 4 clause.

### Status: CLOSED (lemmas; this item has no endpoint Prop)

- Superseded statements: Item 3 (0379bac08) restated the three lemmas below.  The bound is now `exp (N·(deg − i))`, and
  `exists_places_minpoly_coeff` is about the coefficients of `minpoly L (M^N a)`.  The descriptions below are the
  d2cf04137 versions.

- `GroupApproximation/Kazhdan/GHWCharZeroPlaces.lean` (new):
  - `GHW.exists_places_minpoly_coeff_le`.  Setup: a place `w` of `L` with uniformizer `π`, and `K/L` finite
    separable.  Claim: there are finitely many places `u j` of `K`, each with a uniformizer.  If `u j a ≤ exp N` for
    every `j`, then `w` of every coefficient of `minpoly L a` is at most `exp (N · [K:L])`.
  - `GHW.exists_places_minpoly_coeff_le_family`: the same claim for a finite family of places of `L` at once.
  - `GHW.exists_places_minpoly_coeff d M hM K`.  Setup: `B = ℤ[t_1..t_d]`, `L = Frac B`, `K/L` finite, `M > 0`.
    Claim: there are finitely many places `u j` of `K`, each with a uniformizer.  Suppose `M^e a` is integral over
    `B` and `u j a ≤ exp N` for every `j`.  Then each coefficient `c_i` of `minpoly L a` satisfies
    `M^(N·[K:L]) c_i = G` for some `G ∈ ℤ[t]` of total degree at most `N·[K:L]`.  The places lie over the degree
    place (when `d > 0`) and the `p`-adic places for `p | M`.  Separability is automatic in characteristic 0.
- `GroupApproximation/Algebra/IntegerGaussValuations.lean` (claimed; an orphan from de485d673, in no lane's file
  list): the `p`-adic and total-degree valuations on `ℚ(t_1..t_d)` and clearing denominators
  (`exists_algebraMap_eq`).
  - It had never compiled: `FiniteMultiplicity.of_prime_left` needs `WfDvdMonoid (MvPolynomial (Fin d) ℤ)`.
  - Fixed by importing `Mathlib.Algebra.EuclideanDomain.Int` and `Mathlib.RingTheory.PrincipalIdealDomain`.
- Compiled evidence: probe 0913-024239-39237 (base 3e34da4ea) is PROBE GREEN, with both modules BUILT.
  `exists_places_minpoly_coeff` depends on `[propext, Classical.choice, Quot.sound]`.  The earlier probe
  0913-022359-56894 failed only in IntegerGaussValuations, on the missing instance.

### Route

1. Single place.  `ValuationExtension.exists_places_over` gives the places `u j` over `w`: `u j π < 1`, and an
   element integral at every `u j` has `w`-integral minpoly coefficients.  `π^N a` has `u j ≤ 1`, and
   `IsIntegrallyClosed.minpoly_smul` with `coeff_scaleRoots` gives `w(c_i)·exp(−N(deg−i)) ≤ 1`.
2. Family: `choose`, then `Fintype.equivFin (Σ t, Fin (r t))`.
3. Over ℚ(t):
   - The base places are indexed by `{p // p ∈ M.primeFactors} ⊕ Fin (min d 1)`.
   - `minpoly B (M^e a)` has coefficients in `B` (`minpoly.isIntegrallyClosed_eq_field_fractions'`), equal to
     `M^(e(deg−i)) c_i`.
   - Clearing the `p | M` denominators (`exists_algebraMap_eq`) gives `G`.
   - The degree bound is `degValuation_algebraMap_le_iff`; when `d = 0`, `G` is constant.

### Consumer interface (ghw-assembly)

- `GHWCountablePlaces` takes `AddValuation K (WithTop ℤ)`.  Use:
  - `ValuationWithTopInt.addVal (u j)`;
  - `addVal_eq_one` for the uniformizers;
  - `neg_le_addVal_iff` for the bounds, as in `GHWCharP.hasHaagerupProperty_of_isIntegral`.
- ghw-assembly owns the finiteness of the grid of `G` (Combinatorial Nullstellensatz) and the archimedean places.

### Landed

- d2cf04137: `Kazhdan/GHWCharZeroPlaces.lean`.  Landed unverified; it is green now with the same bytes.
- 321615044: the `Algebra/IntegerGaussValuations.lean` import fix.

### Census and wiring

- Row b6d1590be7ab now also cites the three places lemmas.  It stays `partial`: the char-0 half is open.
- Queued `GroupApproximation.Kazhdan.GHWCharZeroPlaces ghw-charp2 321615044`.  `IntegerGaussValuations` is unwired;
  `BoundedIntegralFinite` and `ValuationExtensionPlaces` are in the `GHWCharPClosed` chain.

### Residual (exact)

- None for this item.
- Still open, owned by ghw-assembly (grid finiteness, archimedean places, assembly):
  `GHWFinitelyGeneratedCharZero : ∀ (F : Type) [Field F] [CharZero F] (s : Set (GL (Fin 2) F)), s.Finite → HasHaagerupProperty.{0, 0} (Subgroup.closure s)`.

## Item 1 (closed): GHWFinitelyGeneratedCharP

### Scope (roster, 09-13)

Closed GHWCharP, the positive-characteristic places of GHW Theorem 4, at the Prop the 857f7e44a
reduction consumes: `GroupApproximation.GHW.GHWFinitelyGeneratedCharP`
(`Kazhdan/GHWTheoremFour.lean`),
`∀ (F : Type) [Field F] (p : ℕ) [Fact p.Prime] [CharP F p] (s : Set (GL (Fin 2) F)), s.Finite → HasHaagerupProperty.{0, 0} (Subgroup.closure s)`.
Printed sentence: tex 1146--1147, "Every countable subgroup of $\mathrm{GL}_2$ over a field has the Haagerup
property~\cite[Theorem~4]{GHW}".  `GHWTheoremFour` itself belongs to ghw-assembly.

### Status: CLOSED

- `theorem ghwFinitelyGeneratedCharP : GHWFinitelyGeneratedCharP` (`Kazhdan/GHWCharPClosed.lean`), with
  `#audit_closed_axioms`.  ghw-assembly reports the audit as `[propext, Classical.choice, Quot.sound]`.
- `theorem printedGHWTheoremFourCharP : PrintedGHWTheoremFourCharP` (`Kazhdan/GHWCharP.lean`): the printed clause over
  fields of prime characteristic, `∀ (F : Type) [Field F] (p : ℕ) [Fact p.Prime] [CharP F p] (Γ : Subgroup (GL (Fin 2) F)), Countable Γ → HasHaagerupProperty.{0, 0} Γ`,
  with `#audit_closed_axioms`.
- Compiled evidence: probe 0913-013742-23843 (run by ghw-assembly; base 79102e615; mods `GHWTheoremFour`,
  `GHWCharPClosed`) is PROBE GREEN.  Its only overlay was `GHWFiniteReduction` (md5 8fc833fd), which is byte-equal to
  origin since ghw-assembly's c2a587f4f.  The import closure of `GHWCharPClosed` has 109 GroupApproximation modules.
  Of these, only `GHWFiniteReduction` changed between 79102e615 and origin b490bf08d, so the origin bytes are the
  green bytes.

### Files

- `GroupApproximation/Kazhdan/GHWCharP.lean`. This is the jacobson draft of 09-12 10:49, byte-identical to
  `attic/sweep-2026-09-12/GroupApproximation/Kazhdan/GHWCharP.lean.txt`; no lane file list claimed it.
  - `hasHaagerupProperty_closure_of_charP`: the finitely generated case.
  - `printedGHWTheoremFourCharP`: countable subgroups in prime characteristic.
- `GroupApproximation/Kazhdan/GHWCharPClosed.lean`, new: `ghwFinitelyGeneratedCharP`.  It is separate so that
  `GHWCharP` does not import `GHWTheoremFour`.
- `GroupApproximation/Kazhdan/GHWEntries.lean`: an older unowned draft in the shared tree and the attic.
  `GHWCharP` does not use it; the lead landed it as an orphan and ghw-assembly owns its dedupe.

### Route (printed GHW route, no literature input)

1. The entries of `s` and of their inverses generate a finitely generated `𝔽_p`-algebra `A`, and every element
   of `⟨s⟩` has its entries in `A`.
2. Noether normalization (`exists_integral_inj_algHom_of_fg`, Mathlib) gives `B = 𝔽_p[t_1..t_d] ↪ A`, integral.
3. `K = L(entries)` with `L = Frac B` is finite over `L`.  An iterated Frobenius maps `K` into a separable
   intermediate field `K'` (`GHWFrobeniusSeparable`, on main, green).
4. The places of `K'` over the total-degree place of `L` leave only finitely many integral elements of bounded
   valuation.  This is `BoundedIntegralFinite.finite_bounded_integral` (on main, green, jacobson 19441736f); it
   uses `ValuationExtensionPlaces` and `TotalDegreeValuation` (green 22f1987d0).
5. `hasHaagerupProperty_of_places` (`GHWPlaces`, root-wired) with no archimedean places.

### Landed

- 7155865b2: `Kazhdan/GHWCharP.lean`, `Kazhdan/GHWCharPClosed.lean`.  Landed unverified; they now compile green
  (above), with no Lean bytes changed since.
- 4626c73f2: this report (first version).

### History

- My own probe of `GHWCharP` and `GHWCharPClosed` failed only in `GHWFiniteReduction`.  Two lines were wrong:
  `Subgroup.map_closure` does not exist at the pin (it is `MonoidHom.map_closure`), and there was a
  `congrArg Subtype.val` type mismatch.  ghw-assembly fixed both at c2a587f4f.
- I also wrote a local rewrite of `GHWCharP`, which was not needed: the origin bytes compile.  I discarded it
  (lane backup only) and landed no Lean change.

### Census

- Row b6d1590be7ab (L1145, graded by ghw-assembly): a `partial` row citing `ghwFinitelyGeneratedCharP`,
  `printedGHWTheoremFourCharP` and `hasHaagerupProperty_closure_of_charP`
  (`metadata/nm-census-rows/ghw-charp2.tsv`).

### Wiring

- Queued `GroupApproximation.Kazhdan.GHWCharPClosed ghw-charp2 7155865b2`.  Its unwired chain is `GHWCharP`,
  `GHWTheoremFour`, `GHWFiniteReduction`, `BoundedIntegralFinite`, `GHWFrobeniusSeparable`, `TotalDegreeValuation`
  and `ValuationExtensionPlaces`.

### Residual (exact)

- None for this item.

## Next

- Item 3 is closed and landed (0379bac08).
- Item 4, Jacobson record: done.  Probe 0913-040230-50292 is queued, and root-wire has the tag.
- Item 4, archimedean split: the bridge `GHW.exists_intPoly_eq_pow_mul_minpoly_coeff` is landed (86635025c) and
  green.  ghw-assembly has the name and needs no piece from me; `Kazhdan/GHWCharZero.lean` stays untouched.
- Residual, owned by ghw-assembly: `GHWFinitelyGeneratedCharZero : ∀ (F : Type) [Field F] [CharZero F] (s : Set (GL (Fin 2) F)), s.Finite → HasHaagerupProperty.{0, 0} (Subgroup.closure s)`.
  Its producer `ghwFinitelyGeneratedCharZero` is on main at add35a53a but has no probe record yet.
- Item 5: C2 is already hull-euler's `card_add_six_le_of_linkedO` (050822843, green).  I wrote no
  duplicate and asked the lead for a replacement piece.
- Census: ghw-assembly closed GHW Theorem 4 (`printedGHWTheoremFour`, 66417a372, green 0913-044200-34335, in the root).
  Row b6d1590be7ab is now `formalized` (58ad1d6e0).
  - It names `printedGHWTheoremFour` and this lane's declarations on its route: `ghwFinitelyGeneratedCharP`,
    `hasHaagerupProperty_closure_of_charP` and `GHW.exists_places_minpoly_coeff`.
  - Three declarations the route does not use are dropped: `printedGHWTheoremFourCharP`,
    `IntegerPlacesMinpoly.exists_places_minpoly_coeff` and `exists_intPoly_eq_pow_mul_minpoly_coeff`.
  - The `partial` census notes under Items 1-3 predate this.
- Item 6: `Estimating/OsinAppendixEulerExteriorLinked.lean` is landed (cbca8029b, green 0913-061116-68489) and queued
  for wiring.  hull-euler has the names.  The summation over components and `ExtPhiData` from a section family stay in
  its assembly.
- Item 7: the LoopCut census and its ccd23ffee addendum have gone to the lead and audit-sec5.  No Lean probe or landing
  until the lead rules on (A).
