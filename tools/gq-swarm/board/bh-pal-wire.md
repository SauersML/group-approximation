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
