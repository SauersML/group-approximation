# bh-pal-integrate
Direction: map the other session's metabelian BH Lean chain for the Palomar megapair, own root wiring for green BH/Palomar modules, and run the Palomar check on request.

**Established.**
- 09:19 map v1, 8aaed9fea (grep-graded).
- 15:45 map v2, ca4dc92fd: research/artifacts/gq-bh-pal-integrate-metabelian-chain-map.md, BUILD-graded.
  - The trusted MSI build of 3c8b417428 (log on the node: .lake/last-build-gq-bh-pal-integrate.log) is RED, with 32 modules (27 BH, 5 SK).
  - Error index: $GQ/work/bh-pal-integrate/scratch/errindex-3c8b417428.txt. Red list: $GQ/work/bh-pal-integrate/failed.txt.
  - Of the ten frontier-three gaps, NONE is closed by build. Items 1, 5, 9 and 10 are proved in their own files, but their closures hold 5, 2, 3 and 4 red modules. The other six are open.
  - Frontier: `ElemFP.bhNagaoUncond_fpMetabelian_routeA`, with 4 inputs:
    - S1 `Absorption.suslinZLocal_BadStatement`;
    - P1 `∀ p prime, PolyK2NilGapStatementOver (ZMod p) 4`;
    - Z1 `ElemFPCharZero.CharZeroK2SplitGapStatement`;
    - H1 `Envelope.HigmanVCStepBCoreStatement`.
    T2 and T3 follow from the same four, via `finitelyGeneratedMetabelianStatement_of_pieces` and `finitelyGeneratedLinearStatement_of_hosts` (map §6).
  - Green BH modules: Statement.Basic, Statement.API and Products.Hosts only.

**Wiring.** No BH module qualifies for the root (green AND hypothesis-free). No root edit.

**Palomar check.** None requested yet. When bh-pal-surface asks, I run it on MSI through the probe lock.

**Needs.** The 32 reds repaired (owners: bh-pal-wire for BH, ms-green-sk for SK). Then I re-grade gaps 1, 5, 9 and 10 with one probe.

**Dead.** Grep grading of closure-dependent claims: a producer whose closure is red is not closed.

**Sparks.** S1 (Suslin) files have been quiet for 3 h, so they are editable under the 2 h rule. An unowned repair target if the repair lanes stall.
