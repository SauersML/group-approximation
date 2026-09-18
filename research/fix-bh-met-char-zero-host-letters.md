---
id: fix-bh-met-char-zero-host-letters
kind: route
rg: 2
title: "Fix GroupApproximation.BooneHigman.Metabelian.CharZeroHost.Letters: failed to compile definition, consider marking it as 'noncomputable' b (4 errors on main 3c8b417428)"
target: fp-metabelian-groups-satisfy-boone-higman
status: SUPERSEDED
---

**SUPERSEDED by `fix-bhmet-char-zero-host-letters`.** Duplicate fix node for the same module, landed in parallel; its classification and target are merged there. Track this module only on `fix-bhmet-char-zero-host-letters`.

**Module.** `GroupApproximation/BooneHigman/Metabelian/CharZeroHost/Letters.lean`. It is red on origin/main at 3c8b417428 with 4 hard errors, from bh-pal-integrate's trusted MSI build
(error index kept by that lane; see `research/artifacts/gq-bh-pal-integrate-metabelian-chain-map.md`). The file is unchanged on main since then.
It sits in the closure of the metabelian chain (`Metabelian/ChainWiredFrontierThree`, route A
`bhNagaoUncond_fpMetabelian_routeA`), so while it is red, T2/T3 cannot build.

**First errors.**
```
    line 60:4: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'AddMonoidAlgebra.commSemiring', which is 'nonco
    line 115:4: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'sigma', which is 'noncomputable'
    line 123:4: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'AddMonoidAlgebra.nonAssocSemiring', which is '
```

**Kind.** mechanical (Lean/Mathlib drift).

**Owner and repair.** Lane `bh-pal-wire` owns the BooneHigman/Metabelian repairs (LEAN-OWNERS). Its repair of this file is
written but not yet probed: noncomputable sections, `omit … in`, missing Mathlib imports, renamed lemmas, and the proof
fixes listed on its board. The repair is waiting in the serialized MSI probe queue.

**Resolve when.** A trusted build (`gqprobe-lean.sh`) of `GroupApproximation.BooneHigman.Metabelian.CharZeroHost.Letters` is green with no errors, and the repaired bytes are on
main. Then flip `status` to RESOLVED and cite the green commit.
