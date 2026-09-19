# Non-MF manuscript: every hypothesis the Lean endpoints still carry (2026-09-18)

Lane ms-nm-uncond-a. Read from origin/main at ddeea47ea (2026-09-18 ~15:00 CDT): the sentence census
`metadata/NON_MF_SENTENCE_CENSUS.tsv` (717 rows: 528 formalized, 22 partial, the rest definition,
structural, provenance, attribution or status), its map, and `metadata/NON_MF_CENSUS_CONDITIONAL_BASELINE.txt`.
This is a grep-level audit of signatures. It is not a build attestation.

## Method

1. For every declaration cited by a `formalized` or `partial` row (1293 short names), extract its signature
   from origin/main and list each explicit binder `(h… : P)` whose type `P` is a named constant, i.e. a Prop
   hypothesis rather than data.
2. For each such `P`, look for a binder-free producer `theorem x : P` (or a composition of one with a
   conditional theorem whose own hypothesis has a binder-free producer).
3. Cross-check every entry of the conditional register.
4. Check that every cited name exists on main. All 1293 do; the one apparent miss,
   `killsKernelOfDirectlyFinite_mapMatrix`, is declared with explicit universes in
   `Algebra/DirectlyFiniteReflection.lean`.

## Result: one open hypothesis family, Greendlinger

The only hypothesis that has no producer on main is
`GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement` (Osin's Lemma 4.4 at least-area
diagrams). It is the binder `hG` / `hgreendlinger` of `Full/TorsionFreeEndpoints/Closed`,
`TorsionFreeGreendlinger{Leaf,Forms,Sentences}` and the `TheoremCAssembly*` leaves. `Full/GL06/Assembly` reduces
it to two open residuals:
- `Full.GL06e.AllCellsShortEnclosedRefutedBelowSectionStatement`;
- `Full.GL03DKept.gl03dKept_KeptSubwalkCoreStatement`.

These are owned by the other session's GL lanes (touched 16:15–17:28 UTC on 09-18). The W1 waist wall
(`Estimating/OsinGreendlingerWaist*`, `GreendlingerLeaf/AsmWaist`) and 27 of the 31 register entries (the
Osin Lemma 9.4 pieces: `OsinLemma94*`, `GloballyDistinguishedSectionFamily.*`) feed only the Osin-appendix
route to that same statement (`OsinAppendixGreendlingerParts`, `OsinAppendixAssembly`, ...).

Every row that rides it is on §6 (`thm:torsion-free`, `thm:hull`, `lem:saturation`,
`cor:regular-nonmf-algebra`) or on the abstract and introduction sentences that restate §6:
- tex 66, 294, 299 and 305;
- 15 of the 22 partial rows.

## Hypotheses that look open but are closed on main

| Binder type (cited in formalized rows) | Producer on main |
| --- | --- |
| `CoreModelsLEFStatement` (15 cited decls) | `ChainCore.coreModelsLEFStatement` (`NonMFSentences/CoreModelsLEFClosed`) |
| `CoreRingReflectionStatement`, `CoreMFRadicalKillStatement`, `ClopenCrossedProductNonzeroDefectStatement`, `BilateralThreeTransferStatement` | their `_of_coreModels` forms applied to the above; the printed forms are `printedCoreRingReflection_closed`, `printedCoreMFRadical_closed`, `printedBilateralThree_closed` and `printedDynamicRankBudget_closed` (`NonMFSentences/ChainCoreClosures`) |
| `CountableCrossedProductStatement` | `countableCrossedProductStatement` (`ChainCore/ClopenCrossedProductCountableConsumers`) |
| `TransientCellsStatement`, `TransientIdealLocallyMatricialFTwoStatement`, `UnitKernelLocallyFiniteStatement` | `transientCellsStatement_holds`, then `transientIdealLocallyMatricial_of_cells`; `unitKernelLocallyFiniteStatement_holds` |
| `ChainCoreDefectCoverStatement`, `CoreKernelElementaryStatement`, `InvolutionLocalizationRingClause` | `chainCoreDefectCoverStatement_holds`, `coreKernelElementaryStatement_holds`, `involutionLocalizationRingClause_closed` |
| `BilateralThreeCellStatement`, `TorsionDefectTransferStatement`, `ReturnEmbeddingStatement`, `SubshiftCycleConditionLEFInput` | `bilateralThreeCellStatement`, `torsionDefectTransferStatement_holds`, `returnEmbeddingStatement_holds`, `subshiftCycleConditionLEFInput` |
| `NaiveFreeProductAtAcylindricallyHyperbolic`, `DGOTheorem235Printed`, `GerasimovaOsinTheorem11Printed` | `naiveFreeProductAtAcylindricallyHyperbolic`, `dgoTheorem235Printed`, `gerasimovaOsinTheorem11Printed` |
| `TheoremC.KotowskiOllivierStatement` (`hKO`) | `KMSGroup.KotowskiOllivierClosed.kotowskiOllivier_closed` (`#audit_closed_axioms`) |
| `HullSC.RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement` (`hbridge`) | `GGT/HullSCLemma51EmbeddedBridgeHolds` |
| register: limit set ⇒ Osin (`hhard`) | `GGT.OsinClassification.isAcylindricallyHyperbolicOsin_of_limitSet` (`GGT/OsinLimitSetSpelling`) |
| register: `BilateralThree.relativeElementary_killed_of_rootThree_killed` | closed via `printedBilateralThree_closed` |

So §§2–5 (one-sided compression, one-sided inverses, chain recurrence, amenable traces and Clifford lamps)
carry no open named hypothesis at the grep level. The TheoremCAssembly `sorry`s were retired on 2026-09-13
(2c3c8cb40).

## What is left outside Greendlinger

Seven partial rows remain. Each is a route mismatch, not a missing hypothesis: Lean proves the sentence's
conclusion by a different construction than the printed one.
- `lem:transient-matrices`, the printed atom-partition route (rows 1d0f9a56866c, fd026a61f84f,
  46f3810145ee, 5079b22a3633), is work order WO-NM14-2.
- `lem:involution-localization`, the printed block-refinement route (rows 07ab0fbe6cfc, 3468c60b2946,
  6baf73489057), is work order WO-NM14-3.

Both are claimed by lane ms-nm-partial-a (`Full/AtomRepresentat…`, probe queued 09-18).

## Caveats

- This is a signature grep. A producer whose import closure is red on main is not closed, and none of the
  producers above was build-verified in this pass: all fleet probes failed between 14:30 and 15:30 CDT
  (VPN and rsync), and a probe of KotowskiOllivierClosed, HullSCLemma51EmbeddedBridgeHolds,
  OsinLimitSetSpelling, ChainCoreClosures and CoreModelsLEFClosed is queued.
- The binder scan reads only named-constant binders `(h… : P)`. A hypothesis written inline (a ∀-statement
  in a binder) is not seen. The register's `inlined-statement` class is exactly that case; both of its entries
  are accounted for above.

## Live detector run (09-18 16:20 CDT, Slurm msismall job 1326470)

`scripts/sentence_census.py --verify-unconditional` logic, instrumented (timing + per-row output, same
classifier, filters and register), on an origin/main snapshot at 4a734659e: 717 records, 625 classified
(formalized/definition/partial), 11.5 min wall (corpus 499 s, index 172 s, classification 14 s).

- **NEW findings: 0.** **STALE register lines: 0.** **ACCEPTED: 78** occurrences of the 31 register entries.
- By tex line:
  - l.1604 (`prop:bilateral-three`): 1, the `inlined-statement` line for
    `relativeElementary_killed_of_rootThree_killed`;
  - l.2135 (`thm:hull`): 76, all Osin Lemma 9.4 pieces plus the two HullSC `buried-conditional` lines;
  - l.2149 (`lem:saturation`): 1.
- Sections 1–5 up to tex l.1300 (264 formalized rows): **no finding at all.** So there is nothing to discharge
  under `Full/NMUncondA/`.

Detector blind spot: a cited name that `lean_decls.build_index` cannot resolve is skipped silently
(`decl is None: continue`). The grep check above found every cited short name declared on main, but it
did not check full-name resolution.

## The two non-Osin register lines: discharged in Lean, owed only in metadata (09-19)

Both inline premises already have closed producers on main. No Lean is owed. Each finding survives only
because a map row still cites the generic intermediate instead of the closed carrier that applies it.

| Register line | Only citing row | Closed producer of the premise | Carrier already on main | Staged fix |
| --- | --- | --- | --- | --- |
| `inlined-statement …TorsionFreeLimitSetEndpoints.manuscriptSaturationLimitSet_of_leastAreaLeaves` (`hhard`: limit set ⇒ Osin) | 2f55113239ce (`lem:saturation`, tex 1650, partial) | `GGT.OsinClassification.isAcylindricallyHyperbolicOsin_of_limitSet` (`GGT/OsinLimitSetSpelling`) | `TorsionFreeGreendlingerForms.manuscriptSaturationLimitSet_of_greendlinger`, already cited in the same row; its only binder is `hgreendlinger` | drop the intermediate from the row (`work/ms-nm-uncond-a/metadata/`) |
| `inlined-statement …BilateralThree.relativeElementary_killed_of_rootThree_killed` (`hroot`) | 512b53c80bd2 (tex 1595–1596, "Extending by identity…"), formalized. The register text names 7f55f9a11e5a, which no longer cites it | `rootThree_killed_of_cell bilateralThreeCellStatement` | `ChainCoreSweep.printedBilateralThreeRootAddition_closed` (`NonMFSentences/ChainCoreSweepClosed`) | swap the citation, staged by ms-nm-uncond-b (`work/ms-nm-uncond-b/metadata/`) |

Owed, in order. This is the item-0 lander gap: gqland.sh and gqland-lean.sh refuse `metadata/**`.
1. Apply both staged rows to `metadata/NON_MF_SENTENCE_MAP.tsv`.
2. Delete the two register lines.
3. Regenerate the census with `scripts/sentence_census.py` on MSI.
4. Re-run `--verify-unconditional`. Expect 0 new and 0 stale.

The rows lose only the cited names above, and every name kept was already cited by the same row (or by
7f55f9a11e5a, with no finding), so no new finding can appear. After that, every live line of the register
is one of the 29 row-2135 lines that nm-osin94 owns: the Osin Lemma 9.4 pieces, plus the two HullSC `buried-conditional` lines. Those two are closed declarations that bind nothing, and the register records them as classifier false positives.
The Greendlinger residuals themselves belong to nm-gl06e and nm-gl03d.
