---
rg: 2
id: e33-balls-have-no-small-zero-divisors
kind: claim
title: The torsion-free group E_3(3) in SL_3(Z) has no zero divisors supported in radius-two balls over F_2, F_3 or Q
distinct_from:
  promislow-radius4-one-sided-and-integral-separation: that is a unit census on the elementary amenable Promislow group; this is a zero-divisor census on a torsion-free Kazhdan lattice.
  zero-divisor-support-subgroup-host-constraints: that proves which properties a zero-divisor host must violate; this is a bounded computational census on one admissible host.
artifacts:
  - experiments/zero-divisor-tf/zd_sat.py
  - experiments/zero-divisor-tf/runs/e33-p2-r22.json
  - experiments/zero-divisor-tf/runs/e33-p3-r22.json
  - experiments/zero-divisor-tf/runs/e33-p2-r23.json
  - experiments/zero-divisor-tf/runs/e33-p2-r11-control.json
  - experiments/zero-divisor-tf/runs/e33-p3-r11-control.json
---

**ESTABLISHED (exact computation).** Let `H = E_3(3) = <e_ij(3) : i != j>`
in `SL_3(Z)`. It lies in the principal congruence subgroup `Gamma(3)`, so it
is torsion-free. Let `B(r)` be its ball of radius `r` for the generators
`e_ij(+-3)`, so `|B(1)| = 13` and `|B(2)| = 121`.

There are no nonzero `alpha, beta` with `alpha beta = 0` and
`supp alpha, supp beta` contained in `B(2)`, in any of the following
coefficient rings:

1. `F_2` and `F_3`: SAT census, UNSAT. There are 14641 pairs and 8569
   product cells, 5268 of them singletons.
2. `Q`, and every number field with a prime of residue degree one above 2
   or 3. This follows by reduction.

Over `F_2`, and hence over `Q`, there is also no such pair with one support
in `B(2)` and the other in `B(3)`, in either order.
- The census `e33-p2-r23.json` is UNSAT, with `|B(3)| = 1045` and 126445
  pairs.
- The reverse order follows from the anti-automorphism `g -> g^-1`, which
  preserves the symmetric balls and sends `alpha beta = 0` to
  `beta^* alpha^* = 0`.

The `F_3` instance at radii (2,3) exceeded a 420-second cap.

**Controls.** Adjoining `t = diag(-1,-1,1)`, of order 2, the same encoder
answers SAT at radius one over `F_2` and `F_3`, and the returned zero-divisor
pairs pass the exact recomputation. So the encoding does detect zero
divisors.

This is bounded evidence on one admissible host of
`kaplansky-zero-divisor-conjecture`, not a proof on it.
