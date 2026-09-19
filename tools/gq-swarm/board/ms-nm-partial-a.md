# ms-nm-partial-a
Direction: close the first 11 `partial` rows of metadata/NON_MF_SENTENCE_CENSUS.tsv (file order) with unconditional Lean, built on MSI, landed green.

## Rows
- a16637da7249 abb56744db26 0f22bdbc4184 dce7a9ff4e83 (abstract / intro / thm:torsion-free / cor:regular-nonmf-algebra):
  BLOCKED by the W1 waist `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0,0,0}` (hG), same as ms-nm-partial-b's 11.
  hG ⇐ `Full.GL06.relativeGreendlinger_zero_of_allCells_of_core` from GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement and
  GL03DKept.gl03dKept_KeptSubwalkCoreStatement (other session, zone B). A per-row restatement would be a reshape; not done.
- 1d0f9a56866c fd026a61f84f 46f3810145ee 5079b22a3633 (lem:transient-matrices, tex 1510–1517, WO-NM14-2) and
  07ab0fbe6cfc 3468c60b2946 6baf73489057 (lem:involution-localization, tex 1678–1686, WO-NM14-3):
  STALE partial. NM19 (c9c73adca, 14babf077, fa8a1311a, all root-imported) landed the printed atom route after the census (00:16Z).
  New restatements, no hypotheses beyond the printed setting, in Full/NMRegradeA/:
  - TransientAtomSentences: manuscriptSentence_separatingAtomPartition (1d0f), mem_atomBaseSet_iff + manuscriptSentence_firstOccupiedAtomRepresentative (fd02),
    earlierAtomTest + manuscriptSentence_representativeSetClopen (46f3), manuscriptSentence_refineByAtomsExponentsCoefficients (5079).
  - InvolutionAtomBlocks: exists_blockCells_atoms + manuscriptSentence_matrixBlockConstructionRefinedByKC (07ab: the construction over FIRST-ATOM
    representatives, as printed, not NM19's least-exponent cells), manuscriptSentence_choicesConstantOnRepresentativeCells (6baf).
  - 3468 needs nothing new: NM19.generatedClasses_card is the sentence.
  Census rows staged: $GQ/work/ms-nm-partial-a/rows.tsv (map-row format; @SHA@ = landing sha).

## Status
- 15:40 probe queued: NMRegradeA.{TransientAtomSentences, InvolutionAtomBlocks} + NM19 AtomTower, BlockPlacement.
- 16:41 v4 probe cleared by coordinator (queue reset for main-only). NMRegradeA/{TransientAtomSentences,InvolutionAtomBlocks} are on main
  byte-identical (8d6acdcd0c / a2646f3723), NOT yet probed green, NOT root-wired.
- 19:40 re-probe, EMPTY overlay, vs main e6c93a1fe: NMRegradeA x2 + NM19 AtomTower, BlockPlacement.
- Census: staged map rebased on e6c93a1fe (7 rows partial -> formalized) at $GQ/work/ms-nm-partial-a/metadata/{NON_MF_SENTENCE_MAP.tsv,nm-census-rows/ms-nm-partial-a.tsv};
  waits on item 0 (lander refuses metadata/**) and on this probe going green.
- 21:00 SLURM-BLOCKED (group association counter). The 19:36 request (1789778213.65031) stays queued; no error index exists, so there is nothing to fix.
  Next step once the flag clears: read $GQ/state/pq/1789778213.65031.ms-nm-partial-a/result. If it was DEFERRED, re-probe the same 4 targets once, with an empty overlay.
  If green, land the staged census map/rows (item 0) and hand NMRegradeA to ms-map for root wiring.
Rows closed: 0 (7 staged). Rows remaining: all 11. Of those, 4 are blocked on the W1 waist and 7 are waiting on the probe and the census lander.
- 21:05 Following the MS-WORKLIST ruling, ms-nm-uncond-a owns WO-NM14-2 (rows 1d0f9a56866c fd026a61f84f 46f3810145ee 5079b22a3633). I dropped them from my staged map.
  My NMRegradeA/TransientAtomSentences (on main, unprobed) states all 4 sentences over NM19. Draft rows for ms-nm-uncond-a are at $GQ/work/ms-nm-partial-a/rows-for-ms-nm-uncond-a.tsv.
  Nothing exists yet under NonMF/TransientAtoms/, so they can consume these rows or supersede them.
  Staged map now changes 3 rows only (07ab0fbe6cfc 3468c60b2946 6baf73489057).
- 21:20 Coordinator asked for a statement, a proof plan and a Lean skeleton of the relative Greendlinger lemma. NOT done, because it would duplicate main:
  - statement: GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement (Estimating/OsinAppendixSections.lean:122), Osin 4.4 at least-area diagrams;
  - plan and reduction: Full.GL06.relativeGreendlinger_zero_of_allCells_of_core (GL06/Assembly.lean:89), through Osin/Olshanskii Lemma 9.7's induction, down to 2 residuals:
    GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement (AllCellsStatement.lean:55) and GL03DKept.gl03dKept_KeptSubwalkCoreStatement (Core.lean:47,
    a Jordan-region choice on planar maps); alternatives are in Full/NMWire2/Census.
  A new skeleton over these would be a reshape of GL06 (zone B, consume-only), not a discharge.
  Useful non-duplicate work: item 11 (model-test both residuals for vacuity, as CellPocketPinchPos was refuted). Needs builds, so it waits on SLURM.
- 21:25 probe 1789778213.65031 came back DEFERRED (sbatch AssocMaxSubmitJobLimit; SLURM-BLOCKED is still present). Not re-probing until the flag clears. The same 4 targets need one probe then.
