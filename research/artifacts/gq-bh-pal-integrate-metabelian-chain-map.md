# The other session's metabelian Boone–Higman Lean chain: map for the Palomar megapair

Lane `bh-pal-integrate`, 2026-09-18 ~09:20 CDT, read from origin/main at 2a4dc517d (no builds).
Scope: `GroupApproximation/BooneHigman/**` (825 files), owned by another Claude session's
`bh-met-*` lanes. There were about 570 commits there in the 24 hours before this read, the
latest at 14:13 UTC (bh-met-93o).

## 1. Statement surface

- `BooneHigman/Statement/Basic.lean` defines the three targets. T1 is
  `FinitelyPresentedMetabelianStatement`. T2 is `FinitelyGeneratedMetabelianStatement`. T3 is
  `FinitelyGeneratedLinearStatement`: every f.g. subgroup of `GL (Fin n) K`, for any field K,
  embeds in a f.p. simple group.
- `BooneHigman/Statement/API.lean` holds the Mathlib-level API: `IsMetabelianGroup`,
  `EmbedsInFinitelyPresentedSimpleGroup` and closure lemmas. This is the only import of the
  existing pair `Palomar/MetabelianBooneHigmanSolution.lean` (0db476348, 09-13). That Solution
  is still a skeleton of `_of` theorems.

## 2. Endpoints (exact names)

- `Metabelian.Chain.finitelyPresentedMetabelianStatement_of_frontierThree`: T1 from the ten gap
  Statements below (`Metabelian/ChainWiredFrontierThree.lean`, 093b018ce).
- `Metabelian.Chain.metabelianPiecesStatement_of_frontierThree`: T2's pieces from items 1–7.
- `Products.finitelyGeneratedLinearStatement_of_hosts (hlin : LinearHostStatement)
  (henv : FPSelfSimilarEnvelopeStatement)`: T3 (`Products/Hosts.lean`).
- `Metabelian.Chain.linearHostStatement_of_frontierTwo (hS hdiag hone hfield hK2)`:
  `ChainWiredFrontierTwoBase.lean`.
- `Metabelian.Chain.fpSelfSimilarEnvelope_of_frontierTwo (hV hcore hfi)`:
  `ChainWiredFrontierTwo.lean`.

## 3. The ten gap Statements

| # | Statement | Status on main | Evidence |
|---|---|---|---|
| 1 | `Coprimary.PureCharPrimeEHighModuleStatement` | CLOSED | `eHighWittE_pureCharPrimeEHighModule`, `Metabelian/PureCharPrimeEHighWittEWire.lean`; grep finds no sorry or axiom |
| 2 | `Absorption.SuslinLocalHorrocksStatement` | OPEN, active | Suslin monic stabilization and base-3 work (bh-met-93i, st-400), about 35 commits in 6 h |
| 3 | `ElemFP.VdKRowExtensionStatement` | OPEN, active; reduced ⇔ `VdKRowExtSpecPosStatement`, and ⇐ `vdkInj_DiagStatement` | vdK Ω ⇔ stab injectivity (bh-met-93j), about 35 commits in 6 h |
| 4 | `ElemFP.PolyK2CubeNilLocalStatement` | OPEN, active | the K_2 pullback and Karoubi residual (bh-met-91s, 91v), about 26 commits in 6 h |
| 5 | `ElemFP.FieldK2.BruhatBigCellStatement` | CLOSED | `bruhatBigCell`, `Metabelian/ElemFPFieldK2BruhatBigCellEndpoint.lean`; no sorry or axiom |
| 6 | `ElemFPCharZero.CharZeroK2PosStabGenStatement` | OPEN, active | K2(4,Z[1/m]) reduced to rank three (bh-met-93o), about 33 commits in 6 h |
| 7 | `ElemFPCharZero.CharZeroK2CubeGapPosStatement` | OPEN, active | about 32 commits in 6 h |
| 8 | `Envelope.HigmanVSwapSectionStatement` | OPEN, active | Higman VC orbit gap and tau residuals (bh-met-91q), about 30 commits in 6 h |
| 9 | `Envelope.RNRelatorsFiniteCoreStatement` | CLOSED | `rnNF_finiteCore`, `Metabelian/EnvelopeRelatorsNormalFormFinal.lean`; no sorry or axiom |
| 10 | `Envelope.GenTorsionVPerfectStatement` | CLOSED | `genTorsionVPerfect`, `Metabelian/EnvelopeVPerfect.lean`; no sorry or axiom |

"Closed" here means a theorem of exactly that type, with no hypotheses, exists and its file
contains no `sorry`, `admit` or `axiom` by grep. The `#audit_axioms` output was not re-run;
that needs a trusted MSI build. The activity counts are commits in the six hours before
14:15 UTC touching any file that mentions the Statement.

**Consequence.** Four of the ten are closed, so T1 now waits on exactly six Statements: 2, 3, 4,
6, 7 and 8. T3 uses the same machinery through `linearHostStatement_of_frontierTwo` and
`fpSelfSimilarEnvelope_of_frontierTwo`. It does not need item 1, so it waits on the same six.
Nothing on main yet states "T1 and T3 from the six open gaps": there is no `frontierFour` file
or theorem.

## 4. Build and wiring facts

- No `BooneHigman/**` module is imported by the root `GroupApproximation.lean` (6056 imports,
  docstring at l.6119). The `GroupApproximation` lean_lib has no globs. So these modules are
  built only as explicit targets or through Palomar libs
  (`PalomarMetabelianBooneHigman{Challenge,Solution,ModelTests}` in `lakefile.toml`, l.260ff).
  This looks deliberate: many files there are "WIP: swarm-authored Lean (in-progress lanes)"
  commits, and root-importing them would expose every root build to in-flight edits.
- Recommendation for our dirs (`SteinbergFP/`, `BooneHigmanLinear/`, `BHClosure/`,
  `Palomar/BooneHigman*`): follow the same convention. The BH megapair's Solution lib imports
  what it needs directly, and root imports are added only for finished, green,
  hypothesis-free modules (above the `/-!` line, after the cyclecheck preflight and the
  duplicate-declaration scan).
- `Palomar/comparator-metabelian-boone-higman.json` is not in `PALOMAR_PENDING_CONFIGS`
  (`scripts/check_palomar_submission.py` l.200), as the plan notes.
- `formalization.yaml` currently selects `Palomar/comparator-surjunctive-nonsofic.json`.

## 5. Proposed wiring file for our side (not yet written)

`GroupApproximation/BooneHigmanLinear/FrontierFour.lean`, consuming only the other session's
theorems:

- `t1_of_frontierFour (hH hvdk hloc hgen hcube hswap) : FinitelyPresentedMetabelianStatement`,
  defined as `finitelyPresentedMetabelianStatement_of_frontierThree
  eHighWittE_pureCharPrimeEHighModule hH hvdk hloc FieldK2.bruhatBigCell hgen hcube hswap
  rnNF_finiteCore genTorsionVPerfect`.
- `t3_of_frontierFour (hH hvdk hloc hgen hcube hswap) : FinitelyGeneratedLinearStatement`,
  defined as `Products.finitelyGeneratedLinearStatement_of_hosts` applied to two arguments:
  - `linearHostStatement_of_frontierTwo (polynomialSuslin_of_oneVariable (suslinOneVariable_of_patching
    (suslinPatching_of_localHorrocks hH))) (polyK2StabRangeDiag_of_vdkRowExtension hvdk)
    (polyK2OneVarNil_of_cubeLocal hloc) (fieldK2Vanishing_of_bruhatBigCell bruhatBigCell)
    (charZeroStableK2FG_of_basePos_of_cubeGapPos (charZeroK2BasePos_of_stabGen hgen) hcube)`;
  - `fpSelfSimilarEnvelope_of_frontierTwo (higmanVFinSection_of_swapSection hswap)
    (rnFreeSectionCore_of_normalForm (higmanVFP_of_finSection (higmanVFinSection_of_swapSection hswap))
    (rnNormalFormRelators_of_finiteCore rnNF_finiteCore)) (rnFiniteIndex_of_vPerfect genTorsionVPerfect)`.

The names are copied from `ChainWiredFrontierThree.lean`, `ChainWiredFrontierTwo(Base).lean`
and `Products/Hosts.lean`. Namespaces must be checked in the build.
