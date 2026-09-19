# ms-nm-uncond-a
Direction: non-MF manuscript, non-Greendlinger hypotheses and partial rows.
## Register (09-18 14:50, from origin/main ddeea47ea)
- Only loud hypothesis on the non-MF endpoint: hG = RelativeGreendlingerQuasiGeodesicLeastAreaStatement (TorsionFreeEndpoints/Closed), reduced by GL06 to AllCellsShortEnclosedRefutedBelowSection + gl03dKept_KeptSubwalkCore. GL lanes of the other session own it (touched 16:27-17:28Z). W1 waist wall = OsinGreendlingerWaist*, same family. Excluded.
- metadata/NON_MF_CENSUS_CONDITIONAL_BASELINE.txt, 31 accepted findings: 27 are Osin Lemma 9.4 pieces, which feed only the Osin-appendix route to Greendlinger (OsinAppendixGreendlingerParts etc.), so they are the Greendlinger family; hhard (limit set => Osin) is proved by OsinClassification.isAcylindricallyHyperbolicOsin_of_limitSet; the BilateralThree premise is closed via ChainCoreClosures.printedBilateralThree_closed; the HullSC entries bind nothing. So there is NO open non-Greendlinger hypothesis.
- Non-Greendlinger partial rows (7): lem:transient-matrices x4 (WO-NM14-2, printed atom route), lem:involution-localization x3 (WO-NM14-3, printed block-refinement route). Untaken as of 14:50.
## Claimed
- WO-NM14-2 -> GroupApproximation/Manuscript/NonMF/TransientAtoms/
## 09-18 15:40
- LANDED eb15eee05 research/artifacts/gq-ms-nm-hypothesis-register.md: I scanned the signatures of all 1293 census-cited decls plus the 31 register entries. The only open hypothesis is Greendlinger (GL06 residuals: AllCellsShortEnclosedRefutedBelowSection, gl03dKept_KeptSubwalkCore; owned by the GL lanes). Every other named binder has a binder-free producer (the table is in the artifact). The 7 non-Greendlinger partial rows are route mismatches, claimed by ms-nm-partial-a.
- Nothing is left in my scope to discharge. No Lean written.
- Build verification of the producers is pending: probe queued (pid 60683; KotowskiOllivierClosed, HullSCLemma51EmbeddedBridgeHolds, OsinLimitSetSpelling, ChainCoreClosures, CoreModelsLEFClosed, TheoremCAssemblyGreendlingerLeaf). Fleet probes failed 14:30-15:30 on VPN/rsync.
- Blind spot: a hypothesis written inline (a ∀-statement in a binder) is not seen by the binder scan.
## 09-18 16:40 item 8 (unconditional detector, live) DONE
- LANDED c26d53b50. The live --verify-unconditional logic ran on msismall (job 1326470; 11.5 min, 1 CPU) over origin/main 4a734659e: 0 NEW, 0 STALE, 78 ACCEPTED, found only at tex l.1604, 2135 and 2149. There are no findings at tex l<=1300, so NMUncondA/ has nothing to discharge and I wrote no Lean.
- WO-NM14-2: NM19 Full/AtomRepresentatives/{SeparatingAtoms,AtomBaseSet,AtomCells,AtomTower} (00:16-00:27Z, grep sorry-free) already proves the printed atom route, so only a census regrade is owed (item 0 lander gap). ms-nm-partial-a is probing AtomTower and staging the regrade, so I do not duplicate it.
- The build-verification probe (v2) is queued behind about 16 probes.
- MSI leftovers: /projects/standard/hsiehph/sauer354/ms-nm-uncond-a (snapshot and logs). No jobs are running.
