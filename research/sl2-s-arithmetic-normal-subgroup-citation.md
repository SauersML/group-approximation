---
rg: 2
id: sl2-s-arithmetic-normal-subgroup-citation
kind: route
title: Import the Margulis normal subgroup theorem for the rank-two S-arithmetic lattice, with Serre's congruence form
target: sl2-s-arithmetic-noncentral-normal-subgroups-have-finite-index
requires: []
---

`SL_2(Z[1/p])` embeds diagonally as an irreducible lattice in
`G = SL_2(R) x SL_2(Q_p)` (Borel's theorem that `S`-arithmetic
subgroups are lattices; irreducibility because the projection to each
factor is dense).  `G` has no compact factors and rank two, so Margulis'
normal subgroup theorem (Margulis 1991, Ch. IV, Thm 4.9; the
`S`-arithmetic case is included) applies: a normal subgroup `N` of the
lattice is finite or has finite index.  If `N` is finite it is central
(a finite normal subgroup of an irreducible lattice in a group without
compact factors is central, e.g. because its centralizer has finite
index and is therefore Zariski dense in the Zariski closure of the
lattice, which is all of `G` by Borel density).  The only central
elements of `SL_2(Z[1/p])` are `+-1`.  Hence the normal closure of any
non-central element has finite index.  By Serre's congruence subgroup
theorem for `SL_2` over rings of `S`-integers with infinitely many units,
every finite-index subgroup contains a principal congruence subgroup
`Gamma(m)`, and `Z[1/p]/(m) = 0` unless `gcd(m, p) = 1`, so the level may
be taken prime to `p`.

The failure for `SL_2(Z)` recorded in the claim is the classical fact
that `PSL_2(Z) = Z/2 * Z/3` surjects onto the hyperbolic triangle group
`<a, b | a^2, b^3, (ab)^N>` for `N >= 7`, whose kernel is the normal
closure of `(ab)^N`, the image of `u^N`.
