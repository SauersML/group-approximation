# ct-* lanes: the unowned tail of sec:chain-core

Lead: session `nonsofic-existence-49`, launched 2026-09-13 ~16:25 CDT. The user re-issued the order in that session:
formalize every sentence of the non-MF manuscript unconditionally in Lean, with no literature inputs.

## Scope

- tex 1541–1807 at origin/main 68481e4d7, plus the rewritten Introduction paragraph at tex 249–259.
- This is the content added by 73a84cd9c: prop:bilateral-three, lem:involution-localization, cor:dynamic-rank-budget,
  the remark on the two-ended compactification (tex 1769–1792) and the remark on the rank-two limitation of the
  compression method (tex 1794–1807).
- Why it had no owner: the chain-* plans were scoped at 3c64a92ef, which predates 73a84cd9c, and none of the seven
  chain-* reports mentions this content.

## Lanes

Each lane probes and lands only through `nmprobe.sh` and `nmland.sh`, and shares its probe clone with one existing lane.

| lane | target | clone |
|---|---|---|
| ct-bilateral-cell | ring and matrix identities in the proof of prop:bilateral-three (tex 1549–1596) | lix-a |
| ct-bilateral-mf | prop:bilateral-three endpoint (tex 1541–1607), plus the Introduction sentence on GL_3 | ring-b-end |
| ct-involution | lem:involution-localization (tex 1658–1694) | lix-j |
| ct-return-tower | return sections, tower corner, Φ, block flattening (tex 1707–1741) | lix-h |
| ct-rank-budget | cor:dynamic-rank-budget endpoint (tex 1696–1767), plus the Introduction aperiodic sentence | lix-f |
| ct-two-ended | remark tex 1769–1792 | lix-e |
| ct-rank-two-limit | remark tex 1794–1807 | lix-i |
| ct-sentences | census rows and model tests for the block | ring-b-alg |

## Boundaries

- chain-radical keeps thm:core-mf-radical: the kernel identification, local finiteness, and the EL clauses.
  ct-bilateral-mf supplies the prop:bilateral-three endpoint that its GL_n (n ≥ 3) clauses use.
- ct lanes consume lem:transient-matrices, thm:core-ring-reflection and lem:chain-core-models through their owners'
  declaration names on main, or as named Props until those close.
- chain-radical's Introduction keys `684721560ced`, `aac4a95b387b` and `c6f8fb6abe29` hash the paragraph as it read
  before 73a84cd9c. ct-sentences keys only the new GL_3 and aperiodic sentences; the radical sentences stay with
  chain-radical.

## Coordination

ct lanes report to session `nonsofic-existence-49`. Send cross-lane needs, or pieces that need more lanes, to that
session.

## Wave 2 (2026-09-13 ~16:40 CDT): 33 more lanes from session nonsofic-existence-49

The user asked this session for a massive team. Every wave-2 lane runs an ownership check before it builds anything:
it greps origin and the shared tree, reads `lanes/*.files`, `landed.log` and the roster rulings, and first lands a
`CLAIM <piece> <module>` line in its report. A piece a lane of the other swarm landed on within about 3 hours, or holds
in-flight files for, is recorded with its owner and not rebuilt. All landings go through `nmland.sh`, which refuses
clobbers.

| family | lanes | job |
|---|---|---|
| range audit and fix | ms-intro-1..4 (tex 1–357), ms-compress-1..4 (358–739), ms-inverses-1..4 (740–1174), ms-binary (1175–1231), ms-units (1232–1337), ms-traces-1..3 (1808–2106), ms-torsionfree (2107–2507) | sentence ledger; verify each `formalized` row is closed, root-reachable, printed generality, printed route, no literature binder; build the missing carriers in new modules |
| chain-core ranges | ms-core-1..4 (1338–1540), ms-core-5 (1608–1662) | ledger and model tests; build only leaves an owner report lists as unowned, or sentence carriers no key map lists |
| W1 second starts | w1-binder-1..8 | one independent start per residual waist binder (ClassCountInput, UnboundSameCell, CaseOneSameCell, C6′ TwoGonHolds, MultipleEdgePocketRegion, SectionPocketFaceSet, PocketPinchLabelled, GeodesicCollar); new modules only, never owners' files |
| literature sweep | ms-cite-1 (1–1337), ms-cite-2 (1338–2507) | every `\cite` used as a step must have a proved carrier |

## Census findings for the census lane (from ct-sentences, 2026-09-13 ~17:00; details in `ct-sentences.md`)

- The ct block has 121 sentence keys, taken from census merge `merge-0913-160921` (after 73a84cd9c). All 121 are
  `unassigned` on main. Owners are recorded in `metadata/nm-census-rows/ct-sentences.tsv`. chain-radical's rows cover 22 of
  these keys: 10 still match its plan, and 12 were rekeyed by 73a84cd9c.
- Splitter defect 1: the abbreviation guard has no word boundary, so two rows each hold two sentences:
  `ded50f77e36b` ("…killed. Core restriction…") and `5e4354e1556b` ("…trivial. The same reasoning…").
- Splitter defect 2: unnumbered displays are dropped, so eleven fragment rows carry the displayed mathematics (for example
  `e94a545b030a` "Moreover,", `4c62dd1963db` "For $n\ge2$,", `4a0223a24da4` "Put", `10fe7a237145` "The identities"). They
  must not be graded `structural`. The full list is in `ct-sentences.md`.
- A hand audit plus closed `decide +kernel` models (`Dynamics/ChainCoreTailModels`, 313212d8a) found no false printed
  identity in the bilateral cell, the return tower or the two-ended codimension count.

## Findings for the other swarm's lanes (~17:10; details in the ms-core-1, ms-core-3 and ms-core-4 reports)

- **prop:bilateral-three is landed over four piece Props** (`PrintedBilateralThree`, 816a6b699; corollaries d2f3e22b5).
  chain-radical can consume it for the GL_n (n ≥ 3) clauses of thm:core-mf-radical. Its open pieces:
  - `BilateralThreeCellStatement`: ct-bilateral-cell;
  - `ClopenCrossedProductCountableStatement`: ms-core-4, see the next bullet;
  - `ClopenCrossedProductDirectlyFiniteLEFStatement`: chain-reflection;
  - `ClopenCrossedProductNonzeroDefectStatement`: chain-matricial and chain-reflection.
- **chain-core S1 items 3, 4 and 7** (LEF ⇒ DF and SF; GL_n of an LEF ring is LEF, countable ⇒ MF; R_X countable) had no visible
  activity since the 16:00–16:17 ruling gave them to hull-bridge. ms-core-4 takes them in new modules after an ownership
  check. Item 3 yields `LEFStablyFiniteInterface`, which blocks chain-reflection rows 2, 6 and 11.
- **chain-core S1 gap:** no Lean lemma proves uniqueness of Laurent expansions or distinct powers of u; only the module
  docstring asserts them. ms-core-1 takes this in a new module after an ownership check.
- **chain-matricial:**
  - Its planned interface Props already have producers:
    - DefectWanderingInterface ← `Dynamics.isWandering_diff_image` (root-imported);
    - DefectCoverInterface at Y = CR(T) ← hull-euler's unlanded `compl_chainRecurrentSet_subset`;
    - DefectAvoidsCoreInterface ← chain-core's `notMem_diff_image_of_mem` once R_Y is known directly finite, or by a
      direct ε-chain proof at Y = CR(T).
  - Route fidelity: it builds exponent classes before the separating partition, the reverse of the printed order (keys
    `1d0f9a56866c`, `fd026a61f84f`, `ff376e50f433`). Under rule 9 those rows are `partial` unless each printed step has its own carrier.
- **Census grading:** rows `549aa93e832f` and `bba38420cf8b` are `formalized` over ClopenDefectRestriction, which is not
  root-reachable until its wiring wave lands.
- **chain-radical (from ms-core-5, ledger 3ad0e515b):** 73a84cd9c deleted the old GL route ("restriction of any MF hom to
  the elementary subgroup kills the same kernel", which reaches only n ≥ 4). The printed GL lower bound for n ≥ 3 is now
  prop:bilateral-three (key `2b6b9904f2d6`), so module 5 must take clause (ii) of `PrintedBilateralThree`
  (`MFTargetsKillRelativeElementary`) as its GL input. Ten of its key-map sentences were rekeyed; the list is in
  `ms-core-5.md`. Its planned module 4 duplicates `MFRadicalTransport.mfHomKernel_le_ker` and `mfHomKernel_eq_ker_of_le`
  (ct-rank-budget, fbd3fae3c).
- **cor:dynamic-rank-budget is landed over seven residual Props** (`printedDynamicRankBudget_of_residuals`, aadb514ad;
  statement a2cb17f58). The exact spellings are in `Manuscript/NonMFSentences/DynamicRankBudget.lean`; owners should prove at
  those shapes or send ct-rank-budget a different spelling:
  - `CoreRingReflectionStatement`: chain-reflection;
  - `CoreModelsLEFStatement` (IsLEFRing R_Y): chain-itinerary;
  - `CountableCrossedProductStatement`: ms-core-4;
  - `CoreMFRadicalKillStatement`: GL half via prop:bilateral-three (ms-core-5), EL half and local finiteness chain-radical;
  - `BilateralThreeTransferStatement`: ct-bilateral-mf;
  - `UnitKernelLocallyFiniteStatement`: ct-involution;
  - `ReturnEmbeddingStatement`: ct-return-tower, ct-involution and ct-rank-budget.
- **W1 binder 2 is false as spelled (w1-binder-2, from systolic-counts' truth audit):** `OsinLemma94UnboundSameCellStatement`
  quantifies over every eps with no eps0. Hand model at eps = 0: λ = 1/2, c = 3, μ = 1/16, G = ℤ/5 * ℤ/5,
  r = A·h′·x·x⁻¹·h″. `relativeGreendlingerQuasiGeodesicLeastArea_of_openResiduals` still takes it as `hsame`.
  - Hazard for hull-component and hull-count94: `classCovers_of_endLoops` (red since a25fe2383, wire-queue l.707 held) takes
    `hsameCell : Σ same-cell unbound ≤ T·n`. That hypothesis has no producer: along a stretch λX ≤ (1−λ)N + c, so X ≈ (1/λ − 1)N,
    not O(n). The M = 1 fix leaves an undischargeable binder; the factor must sit on the class words.
  - w1-binder-2 claims `Estimating/OsinLemma94ClassCoversSameCellFactor.lean`: from (i) Σ non-self-facing unbound ≤ Σ S_i + L₀·n and
    (ii) Σ same-cell ≤ M₀·Σ non-self-facing + T·n, it gives `Q.ClassCovers (M₀+1) ((M₀+1)·L₀ + T)`.
  - LANDED 2336592ee: `OsinLemma94ClassPolygons.classCovers_of_sameCellFactor`, closed, no residual Props (axioms propext, Classical.choice, Quot.sound).
    Residuals are owned by the other swarm:
    - (i) is `classCovers_of_endLoops` without `hsameCell` (hull-component);
    - (ii) is `OsinUnboundSameCellCount` with M₀ = ⌈1/λ⌉₊ (fff-periodic), which still rests on `OsinLemma94SameCellPocketInput`.
- **W1 binder 5 (w1-binder-5):** LANDED cb5b195c8 `Estimating/OsinPocketCellWalkChain` (the cell pocket walk is a nonempty closed walk:
  the chain and closes fields of `IsNoncrossingClosedWalk`).
  - As spelled on `S.diagram` the binder is circular (configuration (b′)); hull-select's r1 O-equivalent copy is the live form.
  - Open steps: 3 cell edge conditions on the copy; 4 orientation of the face colouring; 5–6 kept relator cell and the region.
- **Range fixes landed from wave 2 (all probe GREEN, queued for wiring):**
  - `MaxInfiniteProperIsometry` 88180a8b8;
  - `JacobsonPresentedRadicalSLUnion` f797a21d6 (tex 1156 display for the presented J);
  - `CentralCoronaCornerExact` 69f7c6533 (the lem:central-corona-corner statement at the printed exactness);
  - `IntroCompressorSentences` ef4e63c90 (four intro sentences at printed generality; six rows regraded in `ms-intro-2.tsv`);
  - `CliffordWitnessHSRemarkGeneral` 0dca11111 (the HS remark for general W);
  - `MFQuotientUnitsDisplaysGeneral` 9f9f5dedc;
  - `RelatedWorkKazhdanRigidity` 4dd8eb24d.
- **W1 binder 1:** w1-binder-1 claims the cutting-side count (Osin (38), cutting half: per polygon #cutting ≤ 4·#entries + 1)
  in `Estimating/OsinLemma94CuttingSides.lean`, over a named planarity Prop (same-face darts form a forest). The roster gives the
  forest lemma to audit-intro, but audit-intro's report (f720ed401) says no lane owns it.
- **Census regrade items:**
  - `a9dd4b90e479` (Hull 3.12): partial → formalized over `printedHullGeneratingSetLimitSet` and `printedHullTheorem312`; this
    retires the `hhard` baseline line.
  - `dab2f2bfe084`: drop the three hbridge two-leaf carriers (hbridge closed at 18682110d) and keep
    `manuscriptSentence_hullCommonQuotient_of_greendlinger`; the note is stale.
  - `77028123cdd6`: the Lean (T) route for Γ̄ is the P13 certificate through the affine quotient, not BHV's example.
  - `c650b0a20b89`: trim the Hull Cor 5.7 carriers and the quoted next sentence.
  - `523f02126056`: regraded over the new `RelatedWorkKazhdanRigidity` (4dd8eb24d; row in `ms-intro-4.tsv`).
  - New carriers:
    - `2d6574150d4d` and `c34115be7c92` (`MFQuotientUnitsDisplaysGeneral`, 9f9f5dedc);
    - `e681972f7114` and `901f1b49e4e9` (`MaxInfiniteProperIsometry`, 88180a8b8).
  - `KazhdanTransportSentences.lean` and `RankTwelveConfiguration.lean` have no audit lines in source.
- **Tex issue for the manuscript owner** (tex 663–664): the second badge of thm:normal-kazhdan names
  `NormalKazhdanPrintedRoute.manuscriptNormalKazhdanRadical_printedRoute`, which carries the old limsup-combination proof.
  The printed proof is the ultrafilter-trace route, closed as
  `GroupApproximation.Manuscript.NonMFSentences.manuscriptNormalKazhdanRadical_ultrafilterRoute` (root-imported; audited
  in Audit/Sec2:446).
