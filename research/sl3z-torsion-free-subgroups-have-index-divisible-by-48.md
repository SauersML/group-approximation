---
rg: 2
id: sl3z-torsion-free-subgroups-have-index-divisible-by-48
kind: claim
title: Every torsion-free finite-index subgroup of SL_3(Z) has index divisible by 48
distinct_from:
  sl3-zp-torsion-free-open-subgroups-have-index-divisible-by-48: that is about torsion-free open subgroups of SL_3(Z_p), one prime at a time; this is about every torsion-free finite-index subgroup of SL_3(Z), including subgroups all of whose p-adic closures have torsion.
  sl3z-strong-atiyah-denominators-divide-48: that is the rank bound 48 obtained from Gamma(3) and Gamma(4); this shows that no torsion-free finite-index subgroup, even one satisfying Strong Atiyah for some other reason, can improve that bound by restriction.
  sl3z-satisfies-strong-atiyah: that is the open statement with denominator 24; this closes one proposed route to it.
---

**ESTABLISHED** by [[sl3z-torsion-free-index-48-coordinate-sylow-proof]].
Not independently reviewed. No novelty is claimed.

Let `G = SL_3(Z)` and let `H <= G` be torsion-free of finite index. Then

    48 divides [G : H].

**Consequence for Strong Atiyah on `SL_3(Z)`.** For a finite-index `H <= G` and a
matrix `A` over `C[G]`, `rk_(N(G))(A) = rk_(N(H))(res A) / [G:H]`. If a family of
torsion-free finite-index subgroups `H_i` satisfies Strong Atiyah over `C`, then
restriction places every rank in `(1/d)Z` with `d = gcd_i [G : H_i]`, and `48`
divides `d`. So Strong Atiyah for torsion-free groups, applied through
finite-index subgroups of `SL_3(Z)`, gives at best the denominator 48 that
`sl3z-strong-atiyah-denominators-divide-48` already has. It cannot give the
conjectured 24.

This kills the first "other idea" of Section 5 of
`research/artifacts/strong-atiyah-kazhdan-groups-2026-09-12.md`: a torsion-free
subgroup of 2-adic index valuation 3 does not exist, whatever its closures.

**Why the one-prime result was not enough.** A torsion-free `H` can have torsion
in every `p`-adic closure, so
`sl3-zp-torsion-free-open-subgroups-have-index-divisible-by-48` does not apply to
it directly. An explicit example at level 15 is
`sl3z-level-15-torsion-free-subgroup-outside-p-adic-hosts`.

**Model tests.**
- `Gamma(3)` has index `5616 = 48 * 117`, and `Gamma(4)` has index `43008 = 48 * 896`.
- The level-15 subgroup has index `65286000 = 48 * 1360125`, with 2-adic
  valuation exactly 4. So 16 is attained by a subgroup whose closures all have
  torsion.
- The bound fails with torsion allowed: the discrete Iwahori subgroup `K_I` has
  index 21.
