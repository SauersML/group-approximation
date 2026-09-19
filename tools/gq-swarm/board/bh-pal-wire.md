## bh-pal-wire (09-18, lane): FrontierFour wiring — PARKED, waiting on upstream green

**Approach.** Wiring only, no new math: `GroupApproximation/BooneHigmanLinear/FrontierFour.lean` states
T1 (f.p. metabelian ↪ f.p. simple) and T3 (f.g. linear over any field ↪ f.p. simple) from ONLY the six
open metabelian-chain gaps (2 SuslinLocalHorrocks, 3 VdKRowExtension, 4 PolyK2CubeNilLocal,
6 CharZeroK2PosStabGen, 7 CharZeroK2CubeGapPos, 8 HigmanVSwapSection), with the four closed ones
(1 eHighWittE_pureCharPrimeEHighModule, 5 bruhatBigCell, 9 rnNF_finiteCore, 10 genTorsionVPerfect)
plugged in, per §5 of research/artifacts/gq-bh-pal-integrate-metabelian-chain-map.md (8aaed9fea).
Consumes the other session's chain only through its endpoint theorems. Not root-imported.

**The `_of` forms (for bh-pal-surface, once landed).** Namespace `GroupApproximation.BooneHigmanLinear`:
- `finitelyPresentedMetabelianStatement_of_frontierFour (hH hvdk hloc hgen hcube hswap) :
  GroupApproximation.BooneHigman.FinitelyPresentedMetabelianStatement`
- `finitelyGeneratedLinearStatement_of_frontierFour (hH hvdk hloc hgen hcube hswap) :
  GroupApproximation.BooneHigman.FinitelyGeneratedLinearStatement`
Binders are `Metabelian.{Absorption.SuslinLocalHorrocks, ElemFP.VdKRowExtension, ElemFP.PolyK2CubeNilLocal,
ElemFPCharZero.CharZeroK2PosStabGen, ElemFPCharZero.CharZeroK2CubeGapPos, Envelope.HigmanVSwapSection}Statement`.
NOT LANDED: do not swap the Solution to these until this board says landed.

**Established.** Nothing landed. Source parked at `$GQ/work/bh-pal-wire/GroupApproximation/BooneHigmanLinear/FrontierFour.lean`
(md5 2bfc29ad…), out of the shared checkout.

**Blocker (verified 09-18 10:40, trusted mutexed MSI build, log .lake/last-build-bhpalwire.log).** The chain
under FrontierFour is red on main: 30 modules fail with hard errors (25 under BooneHigman/Metabelian,
5 under Manuscript/SimpleKazhdanSofic), all byte-identical to origin/main 505b3b720, all in the closure
(579 modules). Leaf example: AffineFPIdentities (Mathlib-only imports, ed60f3ff9 "WIP: affine FP lane").
Red per direct import: ChainWiredFrontierThree 25, ChainWiredFrontierTwo 11, PureCharPrimeEHighWittEWire 5,
BruhatBigCellEndpoint 2, RNNormalFormFinal 3, VPerfect 4, Products.Hosts 0. So items 1, 5, 9, 10 are
closed by grep only; they do not build on main yet. Coordinator: their WIP is in flight; do not edit it.

**Plan.** At most one probe per hour (`$GQ/work/bh-pal-wire/probe.sh`): skip when a Mathlib-only red
module is unchanged and still in the closure; else one trusted remote-build.sh probe of the seven imports.
On UPSTREAM GREEN: trusted MSI build of FrontierFour itself, then gqland-lean.sh, then hand off here and by message.

**Needs.** (1) The metabelian chain's endpoints green on main. (2) A sanctioned way to get a trusted
remote-build.sh build of an unlanded lane file without writing to the shared checkout. Default unless
told otherwise: one invocation with MSI_LOCAL_ROOT set to a fresh snapshot of the checkout plus this file.

**Dead.** None.

**Sparks.** The four grep-"closed" items should be re-graded only by a build: a Statement proof whose
closure is red is not closed.

## 09-18 ~14:55 relaunch (lane): repairing upstream reds myself
- The old probe.sh is retired; I now build via gqprobe-lean.sh.
- All 12 leaf reds are byte-identical to 10:40, so they are still red. Their first errors come from the old MSI log (repo builds with -DwarningAsError=true):
  - mechanical: noncomputable defs, unused auto-included section variables (`omit ... in`), missing imports (Commute.map → Mathlib.Algebra.Group.Commute.Hom; Localization.Away; Subgroup.closure / map_closure; Algebra.fg_adjoin_finset);
  - plus real proof errors in AffineFPModel, EnvelopeCantorAction, PureCharPrimeEBase, CharZeroCoordsDenominators, TorsionFree*, EnvelopeHigmanV*, ElemFPKMRoots, AbsorptionSuslinEuclidKill and PureCharPrimeEHighWittEBase.
- I own the repair of the BooneHigman/Metabelian reds (LEAN-OWNERS). ms-green-sk owns the SK ones.
- bh-pal-integrate: please do not also repair these. I will read your probe log for the fresh red set.

## 09-18 ~16:40 (lane): route A + 25 repairs, probe queued
- FrontierFour has been rewritten for route A, per bh-pal-integrate map v2 (ca4dc92fd). The binders are `S1 : Absorption.suslinZLocal_BadStatement`, `P1 : ∀ p, p.Prime → ElemFP.PolyK2NilGapStatementOver (ZMod p) 4`, `Z1 : ElemFPCharZero.CharZeroK2SplitGapStatement` and `H1 : Envelope.HigmanVCStepBCoreStatement`.
- Exports, in namespace GroupApproximation.BooneHigmanLinear:
  - `finitelyPresentedMetabelianStatement_routeA`, `finitelyGeneratedMetabelianStatement_routeA` and `finitelyGeneratedLinearStatement_routeA`;
  - helpers `envelope_routeA` (H1 only), `linearHost_routeA` (S1, P1, Z1) and `coprimarySplitting_routeA` (no inputs).
- Repairs are written in the work dir, one for each of the 27 BH reds in the 3c8b417428 build:
  - noncomputable sections, `omit … in`, missing imports and renamed lemmas (MonoidHom.map_closure, `(Subgroup.closure_le _).mpr`, Subalgebra.fg_adjoin_finset, MulAut.mul_apply explicit type);
  - `open scoped Matrix`, a struct-field alignment fix and a `smul_mem'` implicit binder;
  - `.elim` on False;
  - in AffineFPModel, typed `Commute.all` and a `Pi.single` ascription;
  - in ArtinHasseAlg, sigma rebuilt through a restricted-conjugation `conjB` plus an explicit CommRing instance;
  - Localization.Away RingHom unification fixed with explicit `(R := …) (S := …)` in CharZeroK2Split and with Set.range in CharZeroCoordsDenominators.
- One gqprobe of FrontierFour is queued in the fleet lock, behind about 16 other probes. More reds will surface downstream of today's first-error set.
- SK reds (5) are ms-green-sk's; FrontierFour stays red until they are green too.

## 09-18 16:24 LANDED d2df12ed9 (red allowed): the 27 BH repairs + route-A FrontierFour
IN-FLIGHT SET (bh-pal-wire owns; fix-bh-a/fix-bh-b please avoid). These are the modules of research/fix-bh-met-*.md that I am fixing:
  M/AbsorptionSuslinEuclidKill.lean
  M/AffineFPIdentities.lean
  M/AffineFPModel.lean
  M/CharPCoordsAssembly.lean
  M/CharPCoordsFreeMul.lean
  M/CharPHost/CarryRecursion.lean
  M/CharPHost/TreeWord.lean
  M/CharZeroCoordsDenominators.lean
  M/CharZeroHost/Letters.lean
  M/CoprimaryModule.lean
  M/ElemFPCharZeroK2Split.lean
  M/ElemFPK2LocalQuillenIdeal.lean
  M/ElemFPK2StabDiagEndpoint.lean
  M/EnvelopeCantorAction.lean
  M/EnvelopeFiniteIndexAbel.lean
  M/EnvelopeGenTorsionNakayama.lean
  M/EnvelopeHigmanVGenFamily.lean
  M/EnvelopeHigmanVSwapGenAll.lean
  M/PureCharPrimeEBase.lean
  M/PureCharPrimeEHighArtinHasseAlg.lean
  M/PureCharPrimeEHighCoprimaryFp.lean
  M/PureCharPrimeEHighWittEBase.lean
  M/PureCharPrimeEHighWittECoeff.lean
  M/PureCharZeroCocycle.lean
  M/PureCharZeroMatrix.lean
  M/TorsionFreeCoprimaryBlock.lean
  M/TorsionFreeNoetherLocalize.lean
  + BooneHigmanLinear/FrontierFour.lean
- The probe (gqprobe-lean, target BooneHigmanLinear.FrontierFour) is queued. When it reports, I will flip the fix nodes of every module that went green to RESOLVED, and repair the next wave of reds downstream.

## 09-18 (after restart), lane: re-probe against current main
- Main (e6c93a1fe) is byte-identical to my 30 work files, so the overlay is now empty.
- A gqprobe-lean v4 run of BooneHigmanLinear.FrontierFour is queued.
- The in-flight set is unchanged (listed above). Fix nodes research/fix-bh-met-*.md will flip on green.

## 09-18 21:13 wave 2 (Slurm blocked, so unprobed)
- Wave-1 verdict (job 1328760): 24 of 27 green, and their nodes are flipped to RESOLVED (168b0c3c35).
- Landed 55aba370a, red allowed: fixes to the 3 still-red modules and the 8 red importers, plus the S1-family statements (SuslinZLocalEndpoint, SuslinZHalfEndpoint), rewritten via generic `*_BadAt` abbrevs to avoid the Localization.Away semiring diamond, and PureCharPrimeSplit.
- IN-FLIGHT (mine): the 3 red modules, the 8 importers, SuslinZLocalEndpoint, SuslinZHalfEndpoint, PureCharPrimeSplit, FrontierFour.
- Next: when state/SLURM-BLOCKED is gone, run one empty-overlay probe of BooneHigmanLinear.FrontierFour.
- Suspect (unverified): suslinR1Prime_MonicStatement and SuslinMonicConstLead use `Polynomial (Chain.SIntPoly m k)` and may hit the same diamond.
