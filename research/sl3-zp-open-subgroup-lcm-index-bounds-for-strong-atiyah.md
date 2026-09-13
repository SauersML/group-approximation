---
rg: 2
id: sl3-zp-open-subgroup-lcm-index-bounds-for-strong-atiyah
kind: claim
title: At odd p every open W in SL_3(Z_p) has 16 dividing lcm(W) times index, while the pro-2 Iwahori has lcm 8 and index 21
distinct_from:
  sl3-zp-torsion-free-open-subgroups-have-index-divisible-by-48: that covers torsion-free open subgroups at every prime; this allows torsion, bounds lcm times index at odd primes, and computes the lcm of the 2-adic Iwahori subgroup.
---

**ESTABLISHED** by [[sl3-zp-open-subgroup-lcm-index-bounds-proof]].

For a group `W` with finite subgroups of bounded order, `lcm(W)` is the lcm of
their orders.

1. For every odd prime `p` and every open subgroup `W <= SL_3(Z_p)`,

       v_2(lcm W) + v_2([SL_3(Z_p) : W]) >= v_2(|SL_3(F_p)|) >= 4.

2. Every finite 2-subgroup of `SL_3(Q_2)` has order at most 8. So the pro-2
   Iwahori subgroup `I <= SL_3(Z_2)`, the preimage of the unitriangular group,
   has `lcm(I) = 8` and index 21.

**Consequence for Strong Atiyah on `SL_3(Z)`.** Suppose Strong Atiyah with
denominator `lcm(W)` holds for an open `W <= SL_3(Z_p)`, viewed as a discrete
group. Put `H = W cap SL_3(Z)`. Density gives `[SL_3(Z) : H] = [SL_3(Z_p) : W]`,
and restriction to `H` followed by induction from `H` to `W` gives

    rk(A) in (1 / (lcm(W) [SL_3(Z_p) : W])) Z    for A over C[SL_3(Z)].

- **Odd primes.** The denominator is divisible by 16. Torsion-free inputs at
  `p = 2` have index divisible by 48, by
  `sl3-zp-torsion-free-open-subgroups-have-index-divisible-by-48`. So no
  combination of these inputs gives a denominator with 2-part below 16. They
  cannot reach 24.
- **`p = 2`.** Strong Atiyah for `I` with denominator 8 would give
  `rk in (1/168)Z`. Together with `Gamma(3)` that is `(1/24)Z`, which is Strong
  Atiyah for `SL_3(Z)`
  (`sl3z-strong-atiyah-iff-discrete-iwahori-denominator-8`).

Among `p`-adic closures, then, an input that reaches denominator 24 must be
2-adic, and its group `W` must have torsion. The imported theorem
`p-adic-analytic-torsion-free-groups-satisfy-strong-atiyah` covers only
torsion-free `W`.
