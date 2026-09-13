# debt-conditional

Lane `debt-conditional` (clone `lix-r`). Scope: the 32 buried-conditional and 27 conditional-debt findings in
`metadata/NON_MF_CENSUS_CONDITIONAL_BASELINE.txt`, lines 213–310 at origin/main. Checked against 87790c4fa; the
baseline is unchanged since 3f71a3a50.

## Status

- No Lean landed. None of the 59 findings has an input outside the walls that a closed producer or closed carrier
  can honestly discharge.
- The 19 findings outside the walls retire by re-routing census rows. The replacement four-leaf declarations are
  already landed. The rows belong to other lanes, and the re-route asks went to main.
- Classification sent to main on 2026-09-13.

## Classification

Numbers are baseline file line numbers. The four walls:

- hgreendlinger = `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0,0,0}`
- hbridge = `HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0,0,0}`
- hKO = `TheoremC.KotowskiOllivierStatement`
- hW = `FinitelyPresentedInfiniteSimpleStatement`

### A. Only the four walls (40): listed, not touched

nm-endpoints re-routes these once the walls close.

- buried-conditional (25): 215 219 222 225 228 231 234 237 248 251 254 258 260 264 266 269 273 277 279 288 291 295
  303 306 309
- conditional-debt (15): 213 217 221 224 226 229 233 236 284 287 290 302 305 308 310

### B. Historical quasi-geodesic or unbounded Lemma 4.4 inputs (13)

| lines | declaration | cited by |
|---|---|---|
| 239/240 | `HullSC.hullOneStepStatement_of_quasiGeodesicLeaves` | hull-respell LINE:1636, 1644 |
| 241/242 | `HullSC.hullBallFormNG_of_quasiGeodesicLeaves` | hull-respell LINE:1636, 1644 |
| 243/244 | `HullSC.hullInputsCorrected_of_quasiGeodesicLeaves` | hull-respell LINE:1636 |
| 246 | `TorsionFreeHullPrintedGeneral.printedHullSmallCancellationCurrent_of_lemma44_of_lemma49` | sec5-sentences row 7 (LINE:1636) |
| 270/271 | `TorsionFreeSectionSentences.manuscriptSentence_saturationPairAndHullAgain_of_leaves` | sec5-sentences row 11 (LINE:1662) |
| 274/275 | `TorsionFreeSectionSentences.manuscriptSentence_saturationApplyHullNoOmega_of_leaves` | sec5-sentences row 12 (LINE:1665) |
| 292/293 | `TorsionFreeSectionSentences.manuscriptSentence_theoremApplySaturationNoOmega_of_leaves` | sec5-sentences row 19 (LINE:1698) |

Why no Lean route exists:

- `RelativeIsoperimetricBridgeQuasiGeodesicStatement` has no producer on origin/main. Its only one was the sorry that
  2c3c8cb40 deleted.
- `UnboundScaledCounterexample.lean:193` refutes `EstimatingUnboundOutputStatement.{0,0,0}`.
- The canonical Lemma 4.4 over `RelWord.IsLemma44Input` has no length bound. The docstring of
  `HullSCLemma44BoundedBridge.lean` says it cannot be fed from the bounded bridge. Every producer it has takes
  inputs that are neither walls nor closed.

### C. Intermediates derived from the walls (6)

| lines | declaration | input and its only producer | cited by |
|---|---|---|---|
| 255 | `TorsionFreeHullParagraphGeneral.manuscriptSentence_hullOneTargetOneRelatorGeneral_of_oneStep` | `HullOneStepStatementGeneral`, from `hullOneStepStatementGeneral_of_leastAreaLeaves` | sec5-sentences row 8 (LINE:1644) |
| 256 | `…manuscriptSentence_hullInductionOnTargetsGeneral_of_oneStep` | same | sec5-sentences row 8 |
| 261 | `HullSC.hullTowerGeneral_of_oneStep` | same | sec5-sentences row 8 |
| 262 | `TorsionFreeSectionSentences.manuscriptSentence_hullKernelRemark` | `HullTower` data, which only the walls produce | sec5-sentences row 8 |
| 280/282 | `GGT.RelHyp.osin24HullStep_of_boundedLeaves` | bounded h44 and hemb from hgeom + hbridge, h49 from hgreendlinger | hull-respell LINE:1675 |

A carrier here would only restate the wall binders without discharging them, so I am not building one.

## Retirement route

`merge_rows.py` unions every lane's declarations for each map key, and `SUPERSEDES` drops only that lane's own
rows. So the owning lanes, or census `overrides.tsv`, must do the re-routing.

1. **sec5-sentences:** SUPERSEDES rows 7, 8, 11, 12 and 19, keeping their other declarations and dropping the
   carriers above. Replacements already landed:
   - LINE:1644: row 27, `printedHullProofParagraph_of_fourLeaves`. Its proof uses `hullKernelRemark` and the
     `_of_leastAreaLeaves` forms.
   - LINE:1662/1665/1698: rows 28/29/30.
   - LINE:1636: nm-endpoints `printedHullTheorem{,Osin,LimitSet}_of_fourLeaves` on 4895f03fdf5f/8aead549f1fe.

   This retires 246 255 256 261 262 270 271 274 275 292 293 (11).
2. **hull-respell:** SUPERSEDES LINE:1636 and 1644 without the three `_of_quasiGeodesicLeaves` declarations, and
   LINE:1675 without `osin24HullStep_of_boundedLeaves`. nm-endpoints `fournierFacioQuotient_of_fourLeaves` already
   cites 8097c371f35d.

   This retires 239 240 241 242 243 244 280 282 (8).

## Stale-baseline warning

- 2c3c8cb40 (2026-09-13 01:46, "Retire the five sorries of TheoremCAssembly") deleted every sorry-tainted
  producer the conditional-debt findings rested on:
  - `estimatingSelectionConstruction`, `estimatingUnboundOutput` and `relativeIsoperimetricBridgeQuasiGeodesic`;
  - `hullRelatorRespelling`, `kotowskiOllivier`, `literatureInputs` and the `hullInputs` chain.
- The last census merge (export 4626c73f2, 01:40) came before that commit.
- Prediction, not verified by a run: at the next checker run all 27 conditional-debt keys go STALE, which is fatal,
  and re-kind to open-predicate or conditional-data. The census lane should re-run on MSI and re-baseline before
  lines are retired by hand.

## Residual Props

The four walls above. This lane builds none of them.

## Next

Waiting on main. If main names a closed producer for an input outside the walls, or other Lean work, I'll add it
to `lanes/debt-conditional.files`, back it up, land it unverified, probe it, and re-land it after a green probe.
Each retired line gets a row noted `retires <kind> <decl>`.
