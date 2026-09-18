---
id: fix-bh-met-char-zero-coords-denominators
kind: route
rg: 2
title: "Fix GroupApproximation.BooneHigman.Metabelian.CharZeroCoordsDenominators: Application type mismatch: The argument (4 errors on main 3c8b417428)"
target: fp-metabelian-groups-satisfy-boone-higman
status: OPEN
---

**Module.** `GroupApproximation/BooneHigman/Metabelian/CharZeroCoordsDenominators.lean`. It is red on origin/main at 3c8b417428 with 4 hard errors, from bh-pal-integrate's trusted MSI build
(error index kept by that lane; see `research/artifacts/gq-bh-pal-integrate-metabelian-chain-map.md`). The file is unchanged on main since then.
It sits in the closure of the metabelian chain (`Metabelian/ChainWiredFrontierThree`, route A
`bhNagaoUncond_fpMetabelian_routeA`), so while it is red, T2/T3 cannot build.

**First errors.**
```
    line 84:43: Application type mismatch: The argument
    line 90:2: Unknown constant `GroupApproximation.BooneHigman.Metabelian.CharZeroHost.mvPolynomial_mem_range_of_den_dvd`
    line 134:6: Unknown identifier `mvPolynomial_mem_range_of_den_dvd`
```

**Kind.** proof error.

**Owner and repair.** Lane `bh-pal-wire` owns the BooneHigman/Metabelian repairs (LEAN-OWNERS). Its repair of this file is
written but not yet probed: noncomputable sections, `omit … in`, missing Mathlib imports, renamed lemmas, and the proof
fixes listed on its board. The repair is waiting in the serialized MSI probe queue.

**Resolve when.** A trusted build (`gqprobe-lean.sh`) of `GroupApproximation.BooneHigman.Metabelian.CharZeroCoordsDenominators` is green with no errors, and the repaired bytes are on
main. Then flip `status` to RESOLVED and cite the green commit.
