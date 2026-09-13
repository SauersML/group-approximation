---
rg: 2
id: sl3z-strong-atiyah-iff-discrete-iwahori-denominator-8
kind: claim
title: SL_3(Z) has Strong Atiyah denominator 24 iff its index-21 discrete Iwahori subgroup has denominator 8, where 16 is already known
distinct_from:
  sl3z-satisfies-strong-atiyah: that is the open statement with denominator 24; this is the established equivalence reducing it to one missing factor of 2 in the ranks over the discrete Iwahori subgroup.
  sl3z-strong-atiyah-denominators-divide-48: that is the bound 48 for SL_3(Z); this is the bound 16 for the index-21 subgroup K_I together with the equivalence between the two sharp denominators.
---

**ESTABLISHED** by [[sl3z-strong-atiyah-iwahori-denominator-8-proof]].

Let `G = SL_3(Z)` and let

    K_I = {g in G : g mod 2 is upper unitriangular},

the preimage of a Sylow 2-subgroup `U` of `SL_3(F_2)`. Write `rk_H` for the von
Neumann rank over `N(H)`, and `lcm(H)` for the lcm of the orders of the finite
subgroups of `H`.

1. `[G : K_I] = 21`. The finite subgroups of `K_I` are 2-groups of order
   dividing 8, and the dihedral group of order 8 occurs. So `lcm(K_I) = 8`.
2. For every matrix `B` over `C[K_I]`, `16 rk_{K_I}(B) in Z`.
3. The following are equivalent:
   - `SL_3(Z)` satisfies Strong Atiyah: `24 rk_G(A) in Z` for every matrix `A`
     over `C[G]`;
   - `K_I` satisfies Strong Atiyah: `8 rk_{K_I}(B) in Z` for every matrix `B`
     over `C[K_I]`.

The same three statements hold with `K_I` replaced by `K''`, the preimage of a
Sylow 2-subgroup of `SL_3(F_3)`, of index 351.

So the gap between the established denominator 48 and the conjectured 24 is
exactly one factor of 2 in the ranks over `K_I`. The reduction is sharp. For
every finite-index `H <= G`, Strong Atiyah for `H` gives `SL_3(Z)` only the
denominator `lcm(H) [G:H]`, and `v_2(lcm H) + v_2([G:H]) >= 3`. `K_I` and `K''`
attain 3, which is `v_2(24)`.
