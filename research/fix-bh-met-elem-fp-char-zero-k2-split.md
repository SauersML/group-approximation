---
id: fix-bh-met-elem-fp-char-zero-k2-split
kind: route
rg: 2
title: "Fix GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2Split: Application type mismatch: The argument (4 errors on main 3c8b417428)"
target: fp-metabelian-groups-satisfy-boone-higman
status: SUPERSEDED
---

**SUPERSEDED by `fix-bhmet-elem-fp-char-zero-k2-split`.** Duplicate fix node for the same module, landed in parallel; its classification and target are merged there. Track this module only on `fix-bhmet-elem-fp-char-zero-k2-split`.

**Module.** `GroupApproximation/BooneHigman/Metabelian/ElemFPCharZeroK2Split.lean`. It is red on origin/main at 3c8b417428 with 4 hard errors, from bh-pal-integrate's trusted MSI build
(error index kept by that lane; see `research/artifacts/gq-bh-pal-integrate-metabelian-chain-map.md`). The file is unchanged on main since then.
It sits in the closure of the metabelian chain (`Metabelian/ChainWiredFrontierThree`, route A
`bhNagaoUncond_fpMetabelian_routeA`), so while it is red, T2/T3 cannot build.

**First errors.**
```
    line 110:6: Application type mismatch: The argument
    line 129:21: Function expected at
    line 134:0: (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached
```

**Kind.** proof error.

**Owner and repair.** Lane `bh-pal-wire` owns the BooneHigman/Metabelian repairs (LEAN-OWNERS). Its repair of this file is
written but not yet probed: noncomputable sections, `omit … in`, missing Mathlib imports, renamed lemmas, and the proof
fixes listed on its board. The repair is waiting in the serialized MSI probe queue.

**Resolve when.** A trusted build (`gqprobe-lean.sh`) of `GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2Split` is green with no errors, and the repaired bytes are on
main. Then flip `status` to RESOLVED and cite the green commit.
