---
rg: 2
id: sl3-large-prime-collapse-from-weak-ucp-stability
kind: route
title: Exactify the lattice part, empty the p-divisible sector with the depth-free bound, and close the coprime sector
target: sl3-large-prime-pair-relative-commutant-collapse
requires:
  - sl3-z-weakly-ucp-stable
  - kazhdan-subgroup-weak-ucp-exactifies-microstates
  - p-divisible-lambda-exact-mass-vanishes-at-large-primes
  - odd-congruence-lambda-exact-sector-collapses
  - coprime-sector-collapse-is-robust-to-small-p-admixture
---

Fix `p >= 11` and a hyperlinear approximation of `G_p`.  By
`sl3-z-weakly-ucp-stable` and `kazhdan-subgroup-weak-ucp-exactifies-microstates`
(applied to the Kazhdan subgroup `Lambda = SL_3(Z)` of `Gamma = SL_3(Z[1/p])`),
the microstates may be taken exact on `Lambda`: their `Lambda`-parts are
genuine representations `rho'_n`, finite-image by superrigidity, hence of
congruence level `p^(D_n) m'_n` by the congruence subgroup property, and the
`h`-twist defect `epsilon_n` on the generators of `C_0 = Lambda cap h^-1 Lambda h`
tends to zero.  `p-divisible-lambda-exact-mass-vanishes-at-large-primes`
gives `a_p(1 - nu_(0,n)) <= epsilon_n^2/kappa_0^2`, where
`a_p=min(4c_p-3,1/3)>0`,
so the `p`-divisible weight `delta_n = 1 - nu_(0,n)` tends to zero, whatever
the depths `D_n`.  Write `rho'_n = rho'_(n,0) (+) rho'_(n,p)` accordingly.
`odd-congruence-lambda-exact-sector-collapses` proves the collapse when
`rho'_(n,p) = 0`, and `coprime-sector-collapse-is-robust-to-small-p-admixture`
extends it to `delta_n -> 0`.  Hence `(RC3-p)`.

The route consumes weak ucp-stability of the SUBGROUP only, never of the
host, in line with `no-published-unconditional-codense-stable-host`.  After
the depth-free theorem and the robust coprime lemma, its only open input is
`sl3-z-weakly-ucp-stable`, the Dogon--Vigdorovich-type stability question
for `SL_3(Z)`.
