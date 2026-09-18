---
id: fix-bh-met-char-p-host-tree-word
kind: route
rg: 2
title: "Fix GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeWord: automatically included section variable(s) unused in theorem `GroupApp (3 errors on main 3c8b417428)"
target: fp-metabelian-groups-satisfy-boone-higman
status: OPEN
---

**Module.** `GroupApproximation/BooneHigman/Metabelian/CharPHost/TreeWord.lean`. It is red on origin/main at 3c8b417428 with 3 hard errors, from bh-pal-integrate's trusted MSI build
(error index kept by that lane; see `research/artifacts/gq-bh-pal-integrate-metabelian-chain-map.md`). The file is unchanged on main since then.
It sits in the closure of the metabelian chain (`Metabelian/ChainWiredFrontierThree`, route A
`bhNagaoUncond_fpMetabelian_routeA`), so while it is red, T2/T3 cannot build.

**First errors.**
```
    line 82:0: automatically included section variable(s) unused in theorem `GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.image_one_apply`:
    line 98:0: automatically included section variable(s) unused in theorem `GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.map_one_shift`:
    line 119:0: automatically included section variable(s) unused in theorem `GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeHost.image_mul`:
```

**Kind.** mechanical (Lean/Mathlib drift).

**Owner and repair.** Lane `bh-pal-wire` owns the BooneHigman/Metabelian repairs (LEAN-OWNERS). Its repair of this file is
written but not yet probed: noncomputable sections, `omit … in`, missing Mathlib imports, renamed lemmas, and the proof
fixes listed on its board. The repair is waiting in the serialized MSI probe queue.

**Resolve when.** A trusted build (`gqprobe-lean.sh`) of `GroupApproximation.BooneHigman.Metabelian.CharPHost.TreeWord` is green with no errors, and the repaired bytes are on
main. Then flip `status` to RESOLVED and cite the green commit.
