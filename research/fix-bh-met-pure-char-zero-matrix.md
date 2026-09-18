---
id: fix-bh-met-pure-char-zero-matrix
kind: route
rg: 2
title: "Fix GroupApproximation.BooneHigman.Metabelian.PureCharZeroMatrix: failed to compile definition, consider marking it as 'noncomputable' b (1 errors on main 3c8b417428)"
target: fp-metabelian-groups-satisfy-boone-higman
status: SUPERSEDED
---

**SUPERSEDED by `fix-bhmet-pure-char-zero-matrix`.** Duplicate fix node for the same module, landed in parallel; its classification and target are merged there. Track this module only on `fix-bhmet-pure-char-zero-matrix`.

**Module.** `GroupApproximation/BooneHigman/Metabelian/PureCharZeroMatrix.lean`. It is red on origin/main at 3c8b417428 with 1 hard errors, from bh-pal-integrate's trusted MSI build
(error index kept by that lane; see `research/artifacts/gq-bh-pal-integrate-metabelian-chain-map.md`). The file is unchanged on main since then.
It sits in the closure of the metabelian chain (`Metabelian/ChainWiredFrontierThree`, route A
`bhNagaoUncond_fpMetabelian_routeA`), so while it is red, T2/T3 cannot build.

**First errors.**
```
    line 76:4: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'GroupRing.affineAction', which is 'noncomputable'
```

**Kind.** mechanical (Lean/Mathlib drift).

**Owner and repair.** Lane `bh-pal-wire` owns the BooneHigman/Metabelian repairs (LEAN-OWNERS). Its repair of this file is
written but not yet probed: noncomputable sections, `omit … in`, missing Mathlib imports, renamed lemmas, and the proof
fixes listed on its board. The repair is waiting in the serialized MSI probe queue.

**Resolve when.** A trusted build (`gqprobe-lean.sh`) of `GroupApproximation.BooneHigman.Metabelian.PureCharZeroMatrix` is green with no errors, and the repaired bytes are on
main. Then flip `status` to RESOLVED and cite the green commit.
