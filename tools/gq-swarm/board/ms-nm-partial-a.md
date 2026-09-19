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
