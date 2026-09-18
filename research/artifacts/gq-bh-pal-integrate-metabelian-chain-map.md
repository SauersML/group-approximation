# The other session's metabelian Boone–Higman Lean chain: map for the Palomar megapair

Lane `bh-pal-integrate`. Version 2, 2026-09-18 ~15:45 CDT. It supersedes version 1 (8aaed9fea, 09:20),
which graded the gaps by grep.

**This version is graded by a build.** One trusted MSI build (`gqprobe-lean.sh`, fleet mutex, log
`.lake/last-build-gq-bh-pal-integrate.log` on the node) was run on origin/main at `3c8b417428`
(19:47Z), with an empty overlay. Its targets were:
- the four "closed" gap modules;
- `ChainWiredFrontierThree`, `ChainWiredFrontierTwo`, `ChainWiredFrontierTwoBase`;
- `Products.Hosts`.

The build ran 4325 jobs and finished at 15:18:58 CDT. It FAILED, with hard errors in 32 modules
(27 under `BooneHigman/Metabelian`, 5 under `Manuscript/SimpleKazhdanSofic`).

Nothing outside those 32 files reported an error. Red closures were computed from the import graph
of `3c8b417428` (27456 import edges), and the only new commit since then (`eb337c60f`) touches no
BH file.

## 1. Headline

- **No gap Statement is closed by a build.** The four items that version 1 called CLOSED (1, 5,
  9, 10) are theorems with the right type and no `sorry` in their own files. But every one of them
  imports red modules, so none of them compiles on main today.
- **The frontier moved.** The smallest conditional root on main is no longer the ten-gap
  `finitelyPresentedMetabelianStatement_of_frontierThree`. It is lane bh-wire-01's
  `ElemFP.bhNagaoUncond_fpMetabelian_routeA` (`Metabelian/ElemFPBhNagaoWireUncondTop.lean`,
  ccd6736db, 17:55Z). That root has **four** open inputs, listed in §3. It is red by build too
  (32 red modules in its closure of 892).
- **T3 rides the same four.** The body of `bhNagaoUncond_fpMetabelian_of_polyFpEFP` builds both
  `Products.FPSelfSimilarEnvelopeStatement` (`henv`) and
  `Chain.linearHostStatement_of_charP_charZero hcP hc0`. Those are exactly the two arguments of
  `Products.finitelyGeneratedLinearStatement_of_hosts`. So T3 (f.g. linear over any field) follows
  from S1, P1, Z1 and H1 with no coprimary input. This is a wiring fact, not yet a theorem on main.
- **`Products.Hosts`, `Statement.Basic` and `Statement.API` are green.** Their closures (8, 1 and 2
  modules) contain no red module. They are statements and `_of` reductions only.

## 2. The ten frontier-three gaps, graded by build

"Red in closure" counts the 32 red modules inside the import closure of the module that holds the
producer.

| # | Statement | Producer on main | Graded by build |
|---|---|---|---|
| 1 | `Coprimary.PureCharPrimeEHighModuleStatement` | `eHighWittE_pureCharPrimeEHighModule` (PureCharPrimeEHighWittEWire) | NOT CLOSED: 5 red in closure (PureCharPrimeEHigh{WittECoeff,WittEBase,CoprimaryFp,ArtinHasseAlg}, TorsionFreeCoprimaryBlock) |
| 2 | `Absorption.SuslinLocalHorrocksStatement` | reductions only | OPEN |
| 3 | `ElemFP.VdKRowExtensionStatement` | reductions only | OPEN |
| 4 | `ElemFP.PolyK2CubeNilLocalStatement` | reductions only | OPEN |
| 5 | `ElemFP.FieldK2.BruhatBigCellStatement` | `bruhatBigCell` (ElemFPFieldK2BruhatBigCellEndpoint) | NOT CLOSED: 2 red in closure (SK LeavittK2.FieldTwoAction, SkRows.SteinbergWeyl.Diagonal) |
| 6 | `ElemFPCharZero.CharZeroK2PosStabGenStatement` | reductions only | OPEN |
| 7 | `ElemFPCharZero.CharZeroK2CubeGapPosStatement` | none | OPEN |
| 8 | `Envelope.HigmanVSwapSectionStatement` | reductions only | OPEN |
| 9 | `Envelope.RNRelatorsFiniteCoreStatement` | `rnNF_finiteCore` (EnvelopeRelatorsNormalFormFinal) | NOT CLOSED: 3 red in closure (EnvelopeHigmanV{GenFamily,SwapGenAll}, EnvelopeCantorAction) |
| 10 | `Envelope.GenTorsionVPerfectStatement` | `genTorsionVPerfect` (EnvelopeVPerfect) | NOT CLOSED: 4 red in closure (EnvelopeFiniteIndexAbel, EnvelopeGenTorsionNakayama, EnvelopeHigmanVSwapGenAll, EnvelopeCantorAction) |

**Sub-residuals with a producer that carries no hypotheses.** Each is a textual closer. None of
them is build-green: their closures hold 32, 5 and 32 red modules.
- `suslinKill_intCoord : SuslinR1FinIntCoordStatement` (SuslinKillEndpoint)
- `czTriOff_triOffStatement : CZStabGenTriOffStatement` (ElemFPCharZeroTriOffEndpoint)
- `higmanVCTauDone_tightEq : HigmanVCTauTightEqStatement` (EnvelopeHigmanVCTauDoneTau)

**What repairs the grades.** Once the 12 red modules named in rows 1, 5, 9 and 10 compile, those
four items become closed by build, and nothing else is needed. 7 of the 12 have errors that look
mechanical (§4).

## 3. The current frontier: route A (bh-wire-01)

`ElemFP.bhNagaoUncond_fpMetabelian_routeA (hS1 hP1 hZ1 hH1) : FinitelyPresentedMetabelianStatement`

| Input | Statement | Replaces |
|---|---|---|
| S1 | `Absorption.suslinZLocal_BadStatement` (Suslin absorption, bad-prime local case) | gap 2 |
| P1 | `∀ p, p.Prime → PolyK2NilGapStatementOver (ZMod p) 4` (char-p K₂ gap pair) | gaps 3 and 4 |
| Z1 | `ElemFPCharZero.CharZeroK2SplitGapStatement` (char-0 K₂ split gap) | gaps 6 and 7 |
| H1 | `Envelope.HigmanVCStepBCoreStatement` (Higman V step-B core) | gap 8 |

The file's own docstring notes that the Nagao work (K₂(N, F_p[X]) = ⊥ for N ≥ 5) removes none of
the four. It gives only the k = 1 base instance inside P1.

The next-smallest root is `stabDiagVdk_fpMetabelian_routeA` (ElemFPStabDiagVdkTop, bh-met-96,
18:01Z). It has five inputs: S1, `PolyK2OneVarNilStatement`, `stabDiagVdk_GeTwoStatement`, Z1
and H1.

## 4. The 32 red modules (hard errors, repo builds with `-DwarningAsError=true`)

The error index (101 error lines) is in `$GQ/work/bh-pal-integrate/scratch/errindex-3c8b417428.txt`.
Every red module was last changed 7–21 h before the build.

Compared with bh-pal-wire's 10:40 build, one module is FIXED: `ElemFPKMRoots` (f8d46d836). Three
are NEW in this closure: ElemFPCharZeroK2Split, ElemFPK2LocalQuillenIdeal, ElemFPK2StabDiagEndpoint.

- **Mechanical errors:**
  - `noncomputable` missing: CoprimaryModule, CharZeroHost.Letters, PureCharZeroMatrix,
    PureCharZeroCocycle, PureCharPrimeEHighCoprimaryFp;
  - unused auto-included section variables, which need `omit … in`: PureCharPrimeEHighWittECoeff,
    CharPHost.TreeWord, CharPHost.CarryRecursion, SK VecProd and FieldTwoAction;
  - missing imports or renamed lemmas: `Subgroup.closure`, `Subgroup.map_closure`,
    `Subgroup.closure_le`, `Localization.Away`, `Algebra.fg_adjoin_finset`, `Eq.map`, in
    EnvelopeFiniteIndexAbel, EnvelopeGenTorsionNakayama, EnvelopeHigmanVGenFamily,
    CharPCoordsFreeMul, CharPCoordsAssembly and AffineFPIdentities.
- **Real proof errors:**
  - type mismatches or unsolved goals: AffineFPModel, PureCharPrimeEBase,
    PureCharPrimeEHighArtinHasseAlg (heartbeat timeout plus a missing `eHighArtinHasse_sigma`),
    PureCharPrimeEHighWittEBase, EnvelopeHigmanVSwapGenAll, EnvelopeCantorAction;
  - syntax: TorsionFreeCoprimaryBlock, TorsionFreeNoetherLocalize;
  - still to be read: CharZeroCoordsDenominators, ElemFPCharZeroK2Split, ElemFPK2StabDiagEndpoint,
    ElemFPK2LocalQuillenIdeal, AbsorptionSuslinEuclidKill, SK MatrixId, Vectors and
    SteinbergWeyl.Diagonal.
- **Repair owners** (`$GQ/board/LEAN-OWNERS.md`): bh-pal-wire owns the BooneHigman/Metabelian reds,
  and ms-green-sk owns the five SK reds. This lane does not repair them.

## 5. Which bh-met lanes are active, by gap

The source is the origin/main log for the ten hours before 19:50Z, filtered to commits tagged with
a lane. Most commits in this tree carry no lane tag ("WIP swarm").

| Gap family | Tagged lanes (commits) | Last touched | Commits, last 3 h |
|---|---|---|---|
| 2 Suslin (→ S1) | bh-met-93i (6), 92t (4), 91o (3) | ~3 h ago | 0 |
| 3 vdK / stable-range diagonal (→ P1) | bh-met-92t (3), 93h (2), 96 (2) | ~1.8 h ago | 3 |
| 4 polynomial K₂ nil (→ P1) | bh-met-94e (3), bh-wire-01 (3), 93h (3), 93d, 93v; st-448/495/496 | ~1.9 h ago | 15 |
| 6/7 char-0 K₂ (→ Z1) | bh-met-95 (CzBaseFGSqfree), 93v, 93q, 93y | ~1.7 h ago | 1 |
| 8 Higman V (→ H1) | bh-met-92d (4), 91q (3), 91s (3), 92m (3) | ~2.8 h ago | 3 |

Gaps 3/4 (P1) are the busiest. Suslin (S1) has been quiet for three hours. By the swarm rule
(no edits to files the other session changed in the last 2 h), S1 files are editable now; P1
files mostly are not.

## 6. Wiring and Palomar consequences

- **Root.**
  - No BooneHigman module is root-imported, and none qualifies: only green, hypothesis-free
    modules may be.
  - The only green BH modules are Statement.Basic, Statement.API and Products.Hosts, and those
    are definitions and `_of` reductions.
  - No root edit this pass.
- **bh-pal-wire's `FrontierFour.lean`.** It still targets the six-gap interface of version 1.
  The better target is route A:
  - `t1 := bhNagaoUncond_fpMetabelian_routeA hS1 hP1 hZ1 hH1`;
  - `t2 := Products.finitelyGeneratedMetabelianStatement_of_pieces hpieces henv`, with `hpieces` the
    `Coprimary.metabelianPieces_of_splitting …` term from the same body;
  - `t3 := Products.finitelyGeneratedLinearStatement_of_hosts
    (Chain.linearHostStatement_of_charP_charZero hcP hc0) henv`, with `hcP`, `hc0` and `henv`
    built exactly as in the body of `bhNagaoUncond_fpMetabelian_of_polyFpEFP`.

  Either form stays red until the chain's reds are repaired.
- **bh-pal-surface's Solution.** Its `_of` binders should become S1, P1, Z1 and H1 (named
  Statements) once bh-pal-wire lands.
- **Honest status for the megasubmission.** T1, T2 and T3 are conditional on four named
  Statements, and are not buildable on main today.
