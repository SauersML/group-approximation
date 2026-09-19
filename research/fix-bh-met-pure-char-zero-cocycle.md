---
id: fix-bh-met-pure-char-zero-cocycle
kind: claim
rg: 2
title: "Fix GroupApproximation.BooneHigman.Metabelian.PureCharZeroCocycle: failed to compile definition, consider marking it as 'noncomputable' b (1 errors on main 3c8b417428)"
---

Recorded against `fp-metabelian-groups-satisfy-boone-higman` (it was a route with no prerequisites listed, which the checker would read as a complete proof of `fp-metabelian-groups-satisfy-boone-higman`).

**SUPERSEDED by `fix-bhmet-pure-char-zero-cocycle`.** Duplicate fix node for the same module, landed in parallel; its classification and target are merged there. Track this module only on `fix-bhmet-pure-char-zero-cocycle`.

**Module.** `GroupApproximation/BooneHigman/Metabelian/PureCharZeroCocycle.lean`. It is red on origin/main at 3c8b417428 with 1 hard errors, from bh-pal-integrate's trusted MSI build
(error index kept by that lane; see `research/artifacts/gq-bh-pal-integrate-metabelian-chain-map.md`). The file is unchanged on main since then.
It sits in the closure of the metabelian chain (`Metabelian/ChainWiredFrontierThree`, route A
`bhNagaoUncond_fpMetabelian_routeA`), so while it is red, T2/T3 cannot build.

**First errors.**
```
    line 53:9: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'MonoidAlgebra.semiring', which is 'noncomputable
```

**Kind.** mechanical (Lean/Mathlib drift).

**Owner and repair.** Lane `bh-pal-wire` owns the BooneHigman/Metabelian repairs (LEAN-OWNERS). Its repair of this file is
written but not yet probed: noncomputable sections, `omit … in`, missing Mathlib imports, renamed lemmas, and the proof
fixes listed on its board. The repair is waiting in the serialized MSI probe queue.

**Resolve when.** A trusted build (`gqprobe-lean.sh`) of `GroupApproximation.BooneHigman.Metabelian.PureCharZeroCocycle` is green with no errors, and the repaired bytes are on
main. Then flip `status` to RESOLVED and cite the green commit.
