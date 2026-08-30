---
rg: 2
id: triangular-hopf-bundles-admit-coherent-dyadic-euler-roots
kind: claim
title: Finite triangular Hopf-bundle towers admit coherent dyadic Euler roots
distinct_from:
  uniformly-doubled-rordam-steps-force-proper-infiniteness: that is an analytic no-go for implementing every halving by uniform multiplicity in the Rordam limit; this proves that integral K-theory and Euler classes themselves do not obstruct a stagewise finite-depth triangular system.
  dyadic-rordam-tower-realizes-finite-car-corner: that proposed one infinite multiplicity tower and is refuted; this replaces the rank-impossible infinite bundle chain by compatible finite triangles whose depth tends to infinity.
artifacts:
  - research/artifacts/stw99-lxvi-triangular-bundle-feasibility-2026-08-30.md
---

There are finite products of spheres `X_K`, line bundles `L_K` on `X_K`,
and positive bundle maps

`Phi_K : Vect(X_K) -> Vect(X_(K+1))`

such that, for every `0 <= m <= K`, the bundles

`eta_(K,m) = 2^(K-m) L_K`

satisfy all three properties

1. `eta_(K,m) ~= 2 eta_(K,m+1)` for `m<K`;
2. `Phi_K(eta_(K,m)) ~= eta_(K+1,m)`;
3. `e(eta_(K,m)) != 0` integrally.

In particular
`e(eta_(K,m)) = e(eta_(K,m+1))^2`, so every finite triangle is a
literal chain of nonvanishing square roots of Euler classes.

The maps are induced by injective diagonal star homomorphisms between the
stable homogeneous algebras `C(X_K) tensor K`.  On the rank quotient of
`K^0`, every `Phi_K` is multiplication by two, while its line-bundle
twist is invertible.  Hence the direct limit contains nonzero positive
classes `q_m` with `q_m = 2q_(m+1)` for every `m`; on ranks these classes
form the standard positive dyadic chain in `Z[1/2]`.

Thus the elementary finite-rank objection to a literal infinite chain
`eta_m ~= 2 eta_(m+1)` is real, but it disappears after triangularizing:
only finitely many roots are required at stage `K`, and the rank is reset
to one on the new diagonal.  Integral K-theory and Chern classes permit
this coherent finite-depth system.  What remains open for the LXVI route
is analytic: incorporating such triangles into a simple multiplier
inductive limit while retaining a finiteness certificate and avoiding the
uniform-doubling proper-infiniteness mechanism.
