---
rg: 2
id: cd-two-group-with-infranormal-kazhdan-pair-proof
kind: route
title: Pull the nine-leaf Leavitt pair back through the Ollivier--Wise graphical Rips cover of the Leavitt unit group
target: cd-two-group-with-infranormal-kazhdan-pair
requires: [ollivier-wise-kazhdan-rips-construction, leavitt-unit-group-finitely-presented, leavitt-unit-group-carries-nontrivial-rigid-defect]
---

**The cover.**
- `R^x` is finitely presented (`leavitt-unit-group-finitely-presented`).
- `ollivier-wise-kazhdan-rips-construction` with `Q = R^x` gives `1 -> N -> G -> R^x -> 1`, with
  `G` finitely presented, torsion-free and `cd G <= 2`, and `N` Kazhdan.
- Write `pi` for the quotient map.

**The pair downstairs.** By `leavitt-unit-group-carries-nontrivial-rigid-defect`, the nine-leaf
configuration gives `Gamma = EL_alpha(R) <= G_L = EL_D(R) <= R^x`.
- Both groups are Kazhdan.
- `Gamma` is infranormal in `G_L`: the compressors `u, v` and `Gamma` lie in its compression
  semigroup and generate `G_L`.
- `Gamma` is not normal in `G_L`.

By `infranormal-nonnormal-has-infinite-compression-orbit`, some compressor is strict; call it `u`.

**The pair upstairs.** Put `Gamma_hat = pi^-1(Gamma)` and `G_hat = pi^-1(G_L)`, and choose a lift
`u_hat` of `u`.
- *Property (T).* `Gamma_hat` and `G_hat` are extensions of the Kazhdan groups `Gamma` and `G_L`
  by the Kazhdan group `N`, hence Kazhdan.
- *Compression.* `N` is normal in `G` and contained in `Gamma_hat`, so
  `u_hat Gamma_hat u_hat^-1 = pi^-1(u Gamma u^-1) <= pi^-1(Gamma) = Gamma_hat`. The inclusion is
  strict because its image is.
- *Infranormal in `G_hat`.* The compression semigroup of `Gamma_hat` contains `Gamma_hat`,
  hence `N`, and lifts of `u` and `v`. The group it generates contains `N` and maps onto
  `<u, v, Gamma> = G_L`, so it is `G_hat`.
- *Not normal.* `pi(Gamma_hat) = Gamma` is not normal in `pi(G_hat) = G_L`.

**Dimension.** `G_hat <= G`, so `G_hat` is torsion-free with `cd G_hat <= 2`. This is the
counterexample to `cd-two-groups-have-no-infranormal-kazhdan-pairs`, with `K = G_hat` (or `G`).

**Model tests.**
- The trivial pair `N <= G` is normal and carries no strict compressor.
- A strict compressor needs a non-normal infranormal image. So the hypothesis is realized by the
  Leavitt data and by no degenerate substitute.

The same pulled-back pair is used in `hyperbolic-kazhdan-group-has-infranormal-kazhdan-subgroup-proof`
with the Belegradek--Osin cover. Only the cover changes. `QED`
