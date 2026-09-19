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

## Doing
- Trusted MSI probe (empty overlay = origin/main as is) of TorsionFreeEndpoints.Closed + NMWire2.Census. The 15:07 CDT run died on the VPN outage and never built. Re-run queued at 15:29 CDT.

## Established
(none yet)
