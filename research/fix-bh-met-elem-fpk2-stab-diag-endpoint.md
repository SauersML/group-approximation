---
id: fix-bh-met-elem-fpk2-stab-diag-endpoint
kind: route
rg: 2
title: "Fix GroupApproximation.BooneHigman.Metabelian.ElemFPK2StabDiagEndpoint: 'change (3 errors on main 3c8b417428)"
target: fp-metabelian-groups-satisfy-boone-higman
status: SUPERSEDED
---

**SUPERSEDED by `fix-bhmet-elem-fpk2-stab-diag-endpoint`.** Duplicate fix node for the same module, landed in parallel; its classification and target are merged there. Track this module only on `fix-bhmet-elem-fpk2-stab-diag-endpoint`.

**Module.** `GroupApproximation/BooneHigman/Metabelian/ElemFPK2StabDiagEndpoint.lean`. It is red on origin/main at 3c8b417428 with 3 hard errors, from bh-pal-integrate's trusted MSI build
(error index kept by that lane; see `research/artifacts/gq-bh-pal-integrate-metabelian-chain-map.md`). The file is unchanged on main since then.
It sits in the closure of the metabelian chain (`Metabelian/ChainWiredFrontierThree`, route A
`bhNagaoUncond_fpMetabelian_routeA`), so while it is red, T2/T3 cannot build.

**First errors.**
```
    line 70:4: 'change
    line 74:4: 'change ⁅stabDiagLeftPerm n R (x i j hij a), stabDiagLeftPerm n R (x k l hkl b)⁆ = 1' tactic does nothing
    line 78:4: 'change
```

**Kind.** proof error.

**Owner and repair.** Lane `bh-pal-wire` owns the BooneHigman/Metabelian repairs (LEAN-OWNERS). Its repair of this file is
written but not yet probed: noncomputable sections, `omit … in`, missing Mathlib imports, renamed lemmas, and the proof
fixes listed on its board. The repair is waiting in the serialized MSI probe queue.

**Resolve when.** A trusted build (`gqprobe-lean.sh`) of `GroupApproximation.BooneHigman.Metabelian.ElemFPK2StabDiagEndpoint` is green with no errors, and the repaired bytes are on
main. Then flip `status` to RESOLVED and cite the green commit.
