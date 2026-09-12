# rescue-lix → endpoint (successor of sp-endpoint), running report, 2026-09-11

## WHERE THE 09-10 IN-FLIGHT LIX WORK WENT (every path below is on origin/main)

| what | commit | state |
|---|---|---|
| sp-* lane reports (cupone, descent, endpoint, evenside-n, lh, oddside-n, relhomotopy, thm) + tools check_general.py, descent_ext.py, descent_lemmas.py | d9a4490a7 | notes |
| KroneckerEquiv, KroneckerContractible, LIXKCount, LIXKMap, LIXKSection, LIXKGenMap, LIXKGenSection, OddPDescentWord/Shift/Complex/Clifford/Pairing, ParityPCoeffBridge, ParityPAxiomGuard, LIXLemmaSixFrameGeneric, LIXPowersAngle | 8cdb6b3fb | COMPILED (gate A) |
| the 38 pass-2 CharClass edits: ChernEulerBundle, ChernRelation, GysinFromLerayHirsch, GysinPair, GysinRanged, LerayHirsch{Bridge,ChartClassGen,Column,Degree,GradedIso,Homotopy,Induction,Natural,NaturalCoeff,ShiftTerm,Squares,TowerBridge,Transport}, MayerVietorisSequence, ProjectiveSpace{Cohomology,Computation,Ring}, Relative{Dual,Excision,HomotopyInvariance,LES,Local,SmallChains}, Thom{BridgeChartHom,BridgeNaturalHyper,BridgeNaturalSquare,ChartSquare,EulerNaturality,FibreRestriction,FieldTwo,HyperSquare,PuncturedPi,PuncturedRecursion} | dd28464fc | COMPILED (gate B, with all 277 origin importers) |
| LIXKPunctured, LIXKGenPunctured, LIXKGenSphere, LIXKRelativeMV, LIXKStepC, LIXKStepCTwo, LIXKStepCWired, LIXShapeGenericRank, LIXStepDGenData, LIXStepDGenParity, LIXStepDGenAxiomCheck, RelHomotopyPrism, RelHomotopyInvariance | 5c0663f0a + dd28464fc | COMPILED (gate B) |
| Analysis/LIXPowers{Pinch,Normalise,Homotopy,Chain,Export} | e76e62198 + 9d5cf111f + 00b07a9b9 | COMPILED (probes C2, C3) |
| CharClass/OddPTupleBd, OddPTupleSlot | e76e62198 | UNVERIFIED, RED: parked by author ("STATUS: PARKED AND RED"), duplicate `tagAt`/`tagAt_single` of the landed OddPTuple; imported by nothing |
| CharClass/OddPDescentDomino, OddPDescentValue | e76e62198 | UNVERIFIED, RED: "not yet elaborated" (sp-descent); Domino has real proof errors (argument order after `add_comm`, `Function.update_eq_self_iff` direction, unknown `eq_update_self_iff`, stuck `NeZero`, unsolved `succ` goals); Value not reached |
| CharClass/LerayHirschCover, Peel, PeelCP, PeelClosed, RankTwo, Shift (generic pass) | attic 8dc05f669 (`attic/inflight/rescue-lix/…`) | NOT compiled: generic Cover needs a coefficient-generic `bijective_lhSum_comap` (LerayHirschMV is still F₂; no K-generic concrete MV sequence). Origin's F₂ versions build green against the generic tower. |
| Palomar/LIXStrongSolution.lean, comparator-lix-strong.json, scripts/PalomarLIXStrong{Axioms,ChallengeType,SolutionType}.lean | 81a64c86f | landed (Palomar surface, pending config) |
| Palomar/LIXStrongChallenge.lean | 70f6d12ce | landed |
| lakefile.toml (two PalomarLIXStrong libs), .github/workflows/palomar-{check,comparator}.yml, scripts/check_palomar_{statement_match.sh,submission.py} | attic 8dc05f669 | verification job running (SLURM 16 cpus) |

Repairs made while rescuing (no statement changed anywhere): `Finsupp.single_eq_of_ne` argument
order + `finsetSum_apply` (OddPDescentPairing); explicit `tendsto_const_nhds (x := Complex.I)`
(LIXPowersAngle); missing import of the audited module (ParityPAxiomGuard); `sub_eq_add_neg` in
two `simpa` (LerayHirschInduction); section-variable order of `isIso_excisionOf`
(RelativeExcision); unused `all_goals simp` (RelHomotopyPrism); `include` before the docstring
(LIXKRelativeMV); `dualMapOf_quasiIso` → `relDualMapOf_quasiIso` in RelativeDual (collided with
CohomologyMayerVietoris on origin, broke 5 importers); `pullEquivOfHomotopyEquivOf K`
(LerayHirschHomotopy); structure fields elaborated in tactic blocks (RelHomotopyInvariance);
`push Not`, `le_or_gt`, `simpa [← hzdef, hz]`, dropped `← hidef`, `lt_or_gt_of_ne hjne.symm`,
four `_`-binders (LIXPowersPinch); `fun _ hy` (LIXPowersHomotopy).

## WIRING TOPS (compiled-only, not imported by the root or by another landed module)

GroupApproximation.Analysis.LIXLemmaSixFrameGeneric, GroupApproximation.CharClass.KroneckerContractible,
GroupApproximation.CharClass.LIXKGenSection, GroupApproximation.CharClass.OddPDescentPairing,
GroupApproximation.CharClass.ParityPAxiomGuard, GroupApproximation.CharClass.LIXKGenPunctured,
GroupApproximation.CharClass.LIXKRelativeMV, GroupApproximation.CharClass.LIXKStepCTwo,
GroupApproximation.CharClass.LIXKStepCWired, GroupApproximation.CharClass.LIXShapeGenericRank,
GroupApproximation.CharClass.LIXStepDGenAxiomCheck, GroupApproximation.CharClass.RelHomotopyInvariance,
GroupApproximation.Analysis.LIXPowersExport.
Do not wire: OddPTupleBd, OddPTupleSlot, OddPDescentDomino, OddPDescentValue (red), ProblemLIXStrongAssembly (unverified until its probe).

## ENDPOINT (scope from 21:20)

- `ProblemLIXStrong.lean`: docstrings corrected (text only; the family was ill-typed and unshifted).
  Agreed family `b k := fun j => CharClass.KGen.bVecK n (k - 1)`.  Attic copy cfbf8ca42; probe after
  the Palomar job.
- `ProblemLIXStrongAssembly.lean` (unverified 852a5e45a): `powersSections`, `powersSections_one`,
  `lemmaTwoHoldsForSections_powersSections_one_iff` (↔ `LIX.Gen.LemmaTwoHolds n`),
  `lemmaTwoHoldsForSections_powersSections_two_one` (theorem, from the mod-2 `CharClass.lemmaTwoHolds`),
  `exists_isSimpleRing_separable_hasK1InjPowerWitness_of_powersSections`,
  `exists_simple_separable_not_k1Inj_of_powersSections`.

## TRAPS

- zsh does not split `$VAR` word lists: pass path lists through `$(cat file)`.
- nmland's lexical scan once refused Palomar challenge holes; the lead now allows `sorry` in `Palomar/*Challenge.lean` only.
- A SLURM gate can be cancelled from outside (job 417774, 19:40 CDT, CANCELLED+ SIGTERM); the remote build leaves no summary, so no compiled evidence is written; relaunch replays the partial artifacts.
- The cs-endpoint lock was held for ~27 min by an unidentified holder (20:20–20:47 CDT); a queued job waits inside its allocation.

## 23:50 CDT: Corollary 4 discharged; ONE named input left

- `ProblemLIXStrongAssemblyCor4.lean` (COMPILED, probe 0911-234757-76086): `powersSections_eq_degreeFamily` (rfl),
  `LemmaTwoHoldsAtPowers n := ∀ p, p.Prime → p ∣ n → ∀ k, ¬ p ∣ k → LemmaTwoHoldsForSections n (powersSections n k)`,
  `lemmaTwoHoldsAtPowers_iff` (glue's per-stage form), `corollary4Powers_powersSections` (from lix-tower's
  `LIX.Gen.corollary4Powers`), `climbedPowersOutside_of_lemmaTwoHoldsAtPowers`,
  `hasK1InjPowerWitness_of_lemmaTwoHoldsAtPowers`, `exists_isSimpleRing_separable_hasK1InjPowerWitness_of_lemmaTwoHoldsAtPowers`,
  `exists_simple_separable_not_k1Inj_of_lemmaTwoHoldsAtPowers`.
- `ProblemLIXStrongAssemblyHalves.lean` (COMPILED, same probe): imports Cor4; glue names fully qualified (rank-two
  `VIdx`/`baseM`/`Vmat` in `CharClass` collide with `CharClass.Gen` under `open`); `lemmaTwoHoldsAtPowers_of_glue`,
  `exists_isSimpleRing_separable_hasK1InjPowerWitness_of_glue`.
- `Palomar/LIXStrongSolution.lean` docstrings (ff690fad2, text only, shared block untouched): the one remaining
  named proposition is `NinetyNineProblems.LemmaTwoHoldsAtPowers n`.
- Wiring tops: `ProblemLIXStrongAssemblyHalves` (reaches Cor4, Assembly, Glue, Diag).
