---
id: fix-bh-met-envelope-higman-v-gen-family
kind: claim
rg: 2
title: "Fix GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVGenFamily: Unknown constant `Subgroup.closure` (6 errors on main 3c8b417428)"
---

Recorded against `fp-metabelian-groups-satisfy-boone-higman` (it was a route with no prerequisites listed, which the checker would read as a complete proof of `fp-metabelian-groups-satisfy-boone-higman`).

**SUPERSEDED by `fix-bhmet-envelope-higman-v-gen-family`.** Duplicate fix node for the same module, landed in parallel; its classification and target are merged there. Track this module only on `fix-bhmet-envelope-higman-v-gen-family`.

**Module.** `GroupApproximation/BooneHigman/Metabelian/EnvelopeHigmanVGenFamily.lean`. It is red on origin/main at 3c8b417428 with 6 hard errors, from bh-pal-integrate's trusted MSI build
(error index kept by that lane; see `research/artifacts/gq-bh-pal-integrate-metabelian-chain-map.md`). The file is unchanged on main since then.
It sits in the closure of the metabelian chain (`Metabelian/ChainWiredFrontierThree`, route A
`bhNagaoUncond_fpMetabelian_routeA`), so while it is red, T2/T3 cannot build.

**First errors.**
```
    line 79:6: Unknown constant `Subgroup.closure`
    line 80:26: Unknown constant `Subgroup.closure`
    line 84:10: Unknown constant `Subgroup.mem_map.mpr`
```

**Kind.** mechanical (Lean/Mathlib drift).

**Owner and repair.** Lane `bh-pal-wire` owns the BooneHigman/Metabelian repairs (LEAN-OWNERS). Its repair of this file is
written but not yet probed: noncomputable sections, `omit … in`, missing Mathlib imports, renamed lemmas, and the proof
fixes listed on its board. The repair is waiting in the serialized MSI probe queue.

**Resolve when.** A trusted build (`gqprobe-lean.sh`) of `GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVGenFamily` is green with no errors, and the repaired bytes are on
main. Then flip `status` to RESOLVED and cite the green commit.
