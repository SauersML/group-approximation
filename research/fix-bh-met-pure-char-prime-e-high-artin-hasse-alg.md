---
id: fix-bh-met-pure-char-prime-e-high-artin-hasse-alg
kind: claim
rg: 2
title: "Fix GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighArtinHasseAlg: automatically included section variable(s) unused in theorem `GroupApp (8 errors on main 3c8b417428)"
---

Recorded against `fp-metabelian-groups-satisfy-boone-higman` (it was a route with no prerequisites listed, which the checker would read as a complete proof of `fp-metabelian-groups-satisfy-boone-higman`).

**SUPERSEDED by `fix-bhmet-pure-char-prime-e-high-artin-hasse-alg`.** Duplicate fix node for the same module, landed in parallel; its classification and target are merged there. Track this module only on `fix-bhmet-pure-char-prime-e-high-artin-hasse-alg`.

**Module.** `GroupApproximation/BooneHigman/Metabelian/PureCharPrimeEHighArtinHasseAlg.lean`. It is red on origin/main at 3c8b417428 with 8 hard errors, from bh-pal-integrate's trusted MSI build
(error index kept by that lane; see `research/artifacts/gq-bh-pal-integrate-metabelian-chain-map.md`). The file is unchanged on main since then.
It sits in the closure of the metabelian chain (`Metabelian/ChainWiredFrontierThree`, route A
`bhNagaoUncond_fpMetabelian_routeA`), so while it is red, T2/T3 cannot build.

**First errors.**
```
    line 113:0: automatically included section variable(s) unused in theorem `GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighArtinHas
    line 142:0: automatically included section variable(s) unused in theorem `GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighArtinHas
    line 217:4: Application type mismatch: The argument
```

**Kind.** mechanical (Lean/Mathlib drift).

**Owner and repair.** Lane `bh-pal-wire` owns the BooneHigman/Metabelian repairs (LEAN-OWNERS). Its repair of this file is
written but not yet probed: noncomputable sections, `omit … in`, missing Mathlib imports, renamed lemmas, and the proof
fixes listed on its board. The repair is waiting in the serialized MSI probe queue.

**Resolve when.** A trusted build (`gqprobe-lean.sh`) of `GroupApproximation.BooneHigman.Metabelian.PureCharPrimeEHighArtinHasseAlg` is green with no errors, and the repaired bytes are on
main. Then flip `status` to RESOLVED and cite the green commit.
