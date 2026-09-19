# ms-nm-uncond-b
Direction: non-MF torsion-free §6 endpoints (TorsionFreeEndpoints bundle: thm:torsion-free + Osin/limit-set variants, thm:hull, lem:saturation, Fournier-Facio paragraph, cor:regular-nonmf-algebra, abstract 78-79, intro 292-293/303-305).

## Map (09-18 19:45Z, from origin/main source, not yet a build)
- Every §6 endpoint in Full/TorsionFreeEndpoints/Closed takes exactly ONE hypothesis: hG = RelativeGreendlingerQuasiGeodesicLeastAreaStatement (Osin Lemma 4.4). There is NO non-Greendlinger hypothesis in the §6 rows (the bundle includes thm:hull itself, so no bypass of Greendlinger exists).
- hG <= GL06.relativeGreendlinger_zero_of_allCells_of_core from two residuals. These ARE the Greendlinger core (Osin Lemma 9.7(b)):
  - binder 5: GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement (Route A), current frontier GL06h8.gl06h8_classPocketStatement; or Route B = Piece06.CellRoseUncutStatement AND one of P07LakeExclusion.{AllCellsShortLoop, CellPocketInnerTwoArcLong, LakeFillOutside}Statement.
  - residual 10: GL03DKept.gl03dKept_KeptSubwalkCoreStatement (or GL06f.RoseRegionMoveSubArc / GL03D.KeptSubwalk / P10RoseExtremalTrim.roseJunctionCore_LobeRemovalStatement).
  - Full list: Full/NMWire2/Census.lean docstring.
- OWNERSHIP: every alternative above is live work of the other session's GL swarm. P10* (residual 10) was last touched 18:36Z, GL06h8 17:04Z, P06RoseUncut 16:35Z, P07LakeExclusion 16:14Z, GL03DKept 16:14Z. Do not duplicate it.

- The partial §6 census rows were checked one by one (2135, 2142, 2149, 2157×2, 2173×2, 2195, 2217×2). Each is partial ONLY through hG:
  - Hull Cor 5.7, Lemma 5.8 and Lemma 3.5 are closed (printedHullCorollary57, printedHullLemma58, printedHullLemma35);
  - Hull Cor 7.4 = printedHullCorollary74_of_greendlinger (its bridge, relativeIsoperimetricBridgeQuasiGeodesicEmbedded_closed, is closed);
  - Fournier-Facio paragraph: every other input is applied closed.
  So "allCells/core" is not a second hypothesis beside Greendlinger. It IS Greendlinger's residual pair (Osin Lemma 9.7(b)).
- The other session's last commit is b1060caf9 at 18:36Z. If it stays idle, the residual leaves (GL06h8 classPocket; GL03DKept core / P10 lobe removal) become unowned. They are planar-map combinatorics, not a one-shot job.

- Main (e6c93a1fe) keeps the conditional Closed.lean (5f08ce4414) and the GL06/Assembly *_of_allCells_of_core. The archived great-ptolemy copies (tools/branch-archive/claude_great-ptolemy-7vplxg/) are the withdrawn binder-free versions that never compiled. Keep main's.
- Agrees with ms-nm-uncond-a's register (eb15eee05). Nothing non-Greendlinger is left to discharge in §6.

## Probe history (targets: TorsionFreeEndpoints.Closed + NMWire2.Census, empty overlay)
- 15:07 CDT v1: never built. The VPN was down.
- 15:28 v1 and 15:51 v2 waiters were stopped by the coordinator during script upgrades.
- 16:41 v4: queue cleared at the move to main-only.
- 19:36 v4 against main e6c93a1fe: batch job 1338076 (2 of 2) hit TIMEOUT before my request started (its log was never created). DEFERRED, with no verdict.
- Now SLURM-BLOCKED (association counter underflow). Not re-probing.

## Established
- No build verdict yet for the conditional §6 chain on main. Nothing landed, no red seen, no FIX-GRAPH entry.
- Next: once SLURM-BLOCKED clears, re-probe the same two targets ONCE. Note: after the merge, 50 min did not cover even request 1 of batch 1338076, so put these targets first or alone in a batch (closure ≈ 2880 modules).

## Item 9: prop:bilateral-three (claimed 21:14 CDT)
- All four pieces of printedBilateralThree_of_pieces have closed producers on main, at source level:
  - cell: bilateralThreeCellStatement (BilateralThreeCellDischarge, #audit_closed_axioms);
  - countable: clopenCrossedProductCountableStatement / ClopenCrossedProduct.countable;
  - DF->LEF and nonzero defect: *_of_coreModels at coreModelsLEFStatement (CoreModelsLEFClosed, #audit_closed_axioms).
  So printedBilateralThree_closed (ChainCoreClosures) is closed, and it is in the root closure via ChainCoreSweepClosed.
- The register finding (inlined-statement relativeElementary_killed_of_rootThree_killed) survives only because row 512b53c80bd2 still cites that generic lemma.
- STAGED (item 0 lander gap): work/ms-nm-uncond-b/metadata/NON_MF_SENTENCE_MAP.rows.tsv (row 512b53c80bd2 -> printedBilateralThreeRootAddition_closed) and NON_MF_CENSUS_CONDITIONAL_BASELINE.remove.txt. MAP_BASE = e6c93a1fe.
- No Lean written or landed. The build attestation is in ms-nm-uncond-a's probe of ChainCoreClosures/CoreModelsLEFClosed.
