# LIX strongest swarm: residual board

Maintained by `lx-integrator`.  Read at origin/main `01b92308d` (2026-09-12 10:04 CDT) by `git grep` at that SHA.
Lanes, prefixes and rules: session `nonsofic-existence-39` scratchpad `lixs/LANES.md`, `lixs/RULES.md`.

States:
- THEOREM means proved on main.
- COMPILED means compiled evidence exists, per its lane report.
- UNVERIFIED means landed but never compiled.
- RED means the last probe failed.
- OPEN means the statement is on main and has no producer.
- NOT AUTHORED means the declaration does not exist on main (`git grep -w`: 0 files).

## Integration baseline

| probe | base | modules | result |
|---|---|---|---|
| lx-integrator 0912-100606-67380 (cs-endpoint, acn112 cores 64-71) | `4c343e664` | `ProblemLIXStrongAssemblyHalves`, `LIXLemmaTwoGenTwo`, `LIXStepDGenReal`, `LIXKGenOfStepC` | PROBE GREEN, 9456 jobs; purge 0; no module rebuilt, all four restored from the trace or cache with the same input hash, so the consumer tops are consistent at that base |

## D1: `NinetyNineProblems.lemmaTwoHoldsAtPowers (n) (hn : 2 ≤ n) : LemmaTwoHoldsAtPowers n`

| item | where | state | owner | sha |
|---|---|---|---|---|
| `LemmaTwoHoldsAtPowers n` (the one named input) | `Manuscript/NinetyNineProblems/ProblemLIXStrongAssemblyCor4.lean:40` | OPEN | lx-endpoint (assembly) | 99893b9 md5 record 0911-234757-76086 |
| `corollary4Powers n hn` | `Analysis/LIXCor4PowersDiag.lean:421` | THEOREM | done | — |
| `ProblemLIXStrongAssemblyTwo` (the p = 2 named Props and `lemmaTwoHoldsAtPowers_two_pow`) | new | NOT AUTHORED | lx-endpoint | — |
| `ProblemLIXStrongAssemblyOddP` (seam and per-prime assembly) | new | NOT AUTHORED | lx-endpoint | — |

### p = 2 (every even n)

| item | where | state | owner |
|---|---|---|---|
| consumer `Gen.lemmaTwoFor_powers_two_lixChernOf` | `CharClass/LIXLemmaTwoGenTwo.lean:45` | COMPILED (lix-evenside-n record 0912-000930-45207) | — |
| `hC := Wu.cartanTotal` | `CharClass/ParityEvenTransport.lean:284` | THEOREM | — |
| `hloc`: `KGen.KZeroLocalData n (e-1) (lixDD n j) hGc hGu hGe` | `CharClass/LIXKGenStepCHalfTop.lean:51` | OPEN | lx-local2b |
| `KGenLocalNonzero … (lixThomClassTerm n hGc hGu)` (implies KZeroLocalData through `exists_localSplit_ne_zero_kgen`) | `CharClass/LIXKGenLocalSplit.lean:63` | OPEN | lx-local2b |
| `LIXKGenLocalHomotopy`, `LIXKGenLocalLegs` | new | NOT AUTHORED | lx-local2a |
| `LIXKGenLocalSquare`, `LIXKGenLocalNonzero` | new | NOT AUTHORED | lx-local2b |
| compiled inputs: `lixKTrivBall`, `lixKLocalPairIsoClosed`, `lixKRes_lixThomClassTerm_ne_zero`, `lixKU`, `lixKULine`, `injective_lixKShrink`, `relPullback_lixKGHomeo_eq_id` | `LIXKGenLocal{Pair,Res,Nbhd,Linear}` | COMPILED | — |
| `data`: `Gen.WuStepDData n (lixDD n j) pY q₁ qodd σ₁ σodd γ` | `CharClass/LIXStepDGenData.lean:80` | OPEN | lx-slice2 |
| field `split`: `Gen.hasSplitting_lixN` | `CharClass/LIXStepDGenSplit.lean:45` | UNVERIFIED (84b833ac2) | lx-slice2 |
| fields `gamma_eq`, `sq_b`, `slice` (rank-n slice value, `SliceGen*`) | new | NOT AUTHORED | lx-slice2 |
| `tx_inj` and the spaces, projections and sphere data (`KnLix.*`) | new `CharClass/CohomologyKunnethLixN*` | NOT AUTHORED | lx-kunneth |

### odd p

| item | where | state | owner |
|---|---|---|---|
| consumer `Gen.lemmaTwoFor_powers_of_stepC_realModP` | `CharClass/LIXStepDGenReal.lean:335` | COMPILED | — |
| `T`: `Gen.RealTorusModP n K pY q₁ qodd σ₁ σodd` (fields `circle_two`, `z_inj`, `PN`, `PY`, `PN_even`, `PY_even`, `PN_zero`, `cartan`, `natural`, `P_t`, `P_x`, `PY_unstable`) | `CharClass/LIXStepDGenReal.lean:130` | OPEN | lx-torusP |
| `data`: `Gen.RealBundleModP p dd T γ` (fields `γ_even`, `a`, `b`, `a_even`, `b_even`, `γ_eq`, `b_low`, `b_deg`, `gen`, `slice`, `c`, `c_isUnit`, `wu`) | `CharClass/LIXStepDGenReal.lean:191` | OPEN | lx-bundleP |
| instance `[∀ j, ExpChar (evenPart K (Y j)) p]` | new | NOT AUTHORED | lx-bundleP |
| consumer `KGen.stepCHalf_of_kZeroStepCDataOf` | `CharClass/LIXKGenOfStepC.lean:152` | COMPILED | — |
| `KGen.KZeroStepCDataOf K n k dd hGc hGu hGe gamma` | `CharClass/LIXKGenOfStepC.lean:134` | OPEN | lx-stepcK-agree (assembly) |
| its field `KGenLocalNonzeroOf K n k … u` | `CharClass/LIXKGenLocalSplitOf.lean:64` | OPEN | lx-stepcK-local |
| its field `LocalClassesAgree (lixKJlocOf …) xloc c` | `CharClass/LIXKCount.lean:94` | OPEN | lx-stepcK-agree |
| its field `lixJEOf … u = lixPiStarOf … gamma` (hclass over K) | `CharClass/LIXKGenOfStepC.lean` | OPEN | lx-stepcK-agree |
| the seam: `htop` link `TotalHOf` ↔ `Hmod K (lixN n dd) (2r)`, `K = ZMod p` with `CharP`, `((k-1+1 : ℕ) : K) ≠ 0`, `0 < lixDD n j i` | new | NOT AUTHORED | lx-endpoint |

### The reduced powers `P^i` (odd p), from scratch

| item | where | state | owner |
|---|---|---|---|
| `OddPDiagonalAug` (`tupD_exists_preimage_stdSimplexTop_zmod`: isDefEq timeout, ZMod diamond) | `CharClass/OddPDiagonalAug.lean:262` | RED (probe 0912-092529-64114) | lx-diag |
| `OddPDiagonal` (Δ0–Δ6), `OddPDiagonalSrc` | `CharClass/OddPDiagonal.lean:57` | UNVERIFIED (7e2fb5081, b07f2e96c) | lx-diag |
| R1 `oddD`, R2 `oddD_cocycle`, R3 `oddD_natural` (`OddPCochain`) | new | NOT AUTHORED | lx-diag |
| R4 `oddD_coboundary` (cylinder), R5 exactness, R6 `redPow`, R7 instability, R8 `redPow_mk` | new | NOT AUTHORED | lx-redpow |
| R9 `redPow_add`, rotated-slot E5 | new | NOT AUTHORED | lx-additive |
| top power `[D_0(u)] = [u ⌣ ⋯ ⌣ u]` (`OddPTopPower`) | new | NOT AUTHORED | lx-toppower |
| P^0: `EvalIsHeadCoeff (ZMod p) ev` | `CharClass/OddPDescentValue.lean:301` | OPEN | lx-toppower |
| descent constant `printedOddPDescentConstant` (`((p−1)/2)!`, a unit) | `CharClass/OddPDescentValue.lean` | COMPILED (eabf84751) | — |
| `psiW`, `psiW_chainMap`, `psiW_counitLeft/Right` | `CharClass/OddPWDiagonal*.lean` | COMPILED | — |
| `OddPShuffle`: `tupRiffleAll`, `tupBlockRotAll`, chain-map and conjugation identities | new | NOT AUTHORED | lx-cartan-a |
| Cartan comparison and class-level Cartan formula (even degrees) | new `OddPComp*`, `OddPCartan*` | NOT AUTHORED | lx-cartan-b |
| total `P` as a ring hom on `Gen.evenPart (ZMod p) X`, `P(h) = h + κ h^p` with κ a unit, naturality | new `OddPTotal*` | NOT AUTHORED | lx-pzero |
| design of the whole block (lemma lists, constants, model tests) | `notes/lix-strong-swarm/design-*.md` | in progress | lx-design |

### Coefficient-K layers

| item | where | state | owner |
|---|---|---|---|
| chart chain over K (`LerayHirschChartGeneral`, `ChartBundleGen`, `ChartHomeo`, `ChartClassIso`, `ChartTautGen` K-forms) | new | NOT AUTHORED | lx-lhK-a |
| `LH.lerayHirschGraded_compactOf K …` (TrivOpen/Bundle/Union/Finite/Compact/RankOne/Embed over K) | new | NOT AUTHORED | lx-lhK-b |
| `CPn.eulerOfBundle_eq_of_bundleIsoOf`, `CPn.eulerOfBundle_pushforward_congrOf` | `CharClass/ChernEulerIsoOf.lean` | UNVERIFIED (77c5176d3) | lx-lhK-b |
| `CPn.bijective_pull_cpBlockInclIterOf` | `CharClass/ProjectiveSpaceStableOf.lean` | UNVERIFIED (77c5176d3) | lx-lhK-b |
| `ChernSplittingOfFlagRelation` (input (d) (i)–(vii)), `hasSplittingP_flag_ofGraded` | new | NOT AUTHORED | lx-splitK |
| `SliceHomogeneousOf`, `SliceValueVOf`, `SliceSplitVOf`, `SliceRootsOf` at rank n | new | NOT AUTHORED | lx-sliceK |
| `KnLix` over a field K (for `RealBundleModP.γ_eq`, `RealTorusModP.z_inj`) | new | NOT AUTHORED | lx-kunneth |

## D2–D4

| item | state | owner |
|---|---|---|
| `Palomar/LIXStrongSolution.lean`: the three challenge theorems verbatim | waits on D1 | lx-endpoint |
| `scripts/check_palomar_submission.py`: move `comparator-lix-strong.json` from pending to enforced | waits on D1 | lx-endpoint |
| `formalization.yaml` strong main_results row | waits on a completed axioms run | lx-endpoint |
| stable finiteness of `LIX.Gen.LIXLimit n` (tracial state, faithful by simplicity) | NOT AUTHORED | lx-stablyfinite |

## Duplicate scan (lx-integrator, MSI mirror at `c3b58d90c`, 832 LIX modules)

Name collisions (the same fully qualified name declared in two files): 6.  All six involve the parked red files, and nothing imports those files.
- `CharClass.tagAt`, `CharClass.tagAt_single`: `OddPTuple` and `OddPTupleBd`.
- `CharClass.tagBdL`, `tagBdL_single`, `tagBdL_tagAt`, `tagBdL_tagBdL`: `OddPTupleBd` and `OddPTupleSlot`.
- lx-diag has been told.

Content duplicates: 47 signature matches.
- Matching rule: distinct names, identical statement text of at least 80 characters.
- Most are definitions with equal binders and type, so they are not duplicate facts.
- Distinct names cause no import error, so these are cleanup, not blockers.

The same-fact pairs among them:

| names | files | owners |
|---|---|---|
| `LH.colTwo` / `colTwoOf`, `LH.lhSum_two_apply` / `…Of`, `LH.lhTerm_index_one` / `…Of`, `LH.lhTerm_index_zero` / `…Of` | `GysinFromGraded`, `LerayHirschRankTwo` | lx-stepcK-agree, lx-lhK-b |
| `exists_smallAnnOf_preimage` / `exists_smallAnn_preimageOf` | `RelativeSplitField`, `CupVanishRepOf` | lx-kunneth |
| `isZero_Hmod_of_isEmptyMV` / `isZero_cohomology_of_isEmptyOf` | `MayerVietorisDisjointOf`, `CohomologyKunnethSphereOf` | lx-lhK-a, lx-kunneth |
| `MVDelta.f_comp_projU/V`, `MVDelta.mvCxInclV_comp_g` / `f_comp_mvCxProjU/V`, `mvCxInclV_comp_g` | `CohomologyDeltaChain`, `MayerVietorisPull*` | lx-lhK-a |
| `Gen.circle_two_sphereOf` / `Gen.circle_two_torusOf` | `LIXStepDGenRealTorus`, `LIXStepDGenRealTorusModel` | lx-torusP |
| `topChernClass_ne_zero_odd_iso` / `topChernClass_ne_zero_odd_local_of_iso` | `ThomStepCOddIso`, `ThomStepCOddLocal` | lx-stepcK-agree |
| `LIX.Gen.matEval_fromBlocks`, `reindex_conjTranspose`, `reindex_mul` / the rank-two `LIX.*` | `LIXCor4PowersStage`, `LIXLemmaSixCor4` | lx-endpoint |

The scanner is `lixs/remote/lix_dupscan.py` in session 39213f46's scratchpad; its MSI copy is `/projects/standard/hsiehph/sauer354/lixs/`.

## Root wiring

Rules agreed with session `nonsofic-existence-3a`:
- Run `tools/nm-swarm/dupcheck.py <tip> <modules>` before each root build and before each push; any DUP line blocks the landing.
- Never land while an `nm-root` SLURM job is running or pending.
- LIX root builds are named `lx-root`.
- Insert only after the last import line and remove nothing.
- No LIX wave until 3a reports that wave bo6h618iu has finished.

## Do not wire (red or parked)

`CharClass/OddPTupleBd`, `CharClass/OddPTupleSlot` (red; the author parked them; duplicates of `tagAt`/`tagAt_single` in `OddPTuple`), `CharClass/OddPDiagonalAug` (red).
