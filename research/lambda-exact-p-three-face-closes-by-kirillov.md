---
rg: 2
id: lambda-exact-p-three-face-closes-by-kirillov
kind: route
title: Every exact lattice sector reduces to coprime level and its relative commutant collapses
target: lambda-exact-face-closes-at-p-three
requires:
  - sl3-primary-exact-congruence-mass-vanishes-at-every-prime
  - odd-congruence-lambda-exact-sector-collapses
artifacts:
  - research/artifacts/sl3-primary-exact-sector-kirillov-tightness-2026-09-08.md
---

The argument works for every prime p, hence for the stated p-three
target and every p=3 modulo 4. Let
pi:SL_3(Z[1/p]) -> U(prod_omega M_n) be a homomorphism whose
SL_3(Z) restriction has genuine finite congruence representatives
sigma_n, and let H_n represent pi(h).

The fixed overlap relations and the primary-vanishing theorem give
genuine coprime representatives beta_n with

    sup_(c in SL_3(Z))||sigma_n(c)-beta_n(c)||_2 ->_omega 0.

Thus pi has exactly the same lattice restriction as a coprime exact
model. The established coprime sector theorem applies to that same
pi and yields

    pi(SL_3(Z))' intersect prod_omega M_n
      = pi(SL_3(Z[1/p]))' intersect prod_omega M_n.

For matrices this proves the target's sequential commutator
statement P3F3: whenever bounded k_n commute with sigma_n(C),
their ultraproduct commutes with pi(h), so
||[k_n,H_n]||_2 ->_omega 0. The same proof works for arbitrary
bounded sequences asymptotically commuting with the lattice.
No regular-trace assumption is needed, but the ambient group
relations used in the coprime Weyl-slot argument must hold.

This route neither uses nor repairs the failed flat-profile or
metaplectic-flux assemblies. Their countermodels and invalidations
remain valid. Only the genuine-exact lattice sector is closed.
The uniformly noncorrectable lattice-microstate sector of the
nonhyperlinear existence problem remains unresolved.
