---
rg: 2
id: free-subgroup-rounding-fails-for-non-normal-fibres
kind: claim
title: Over F_2 wr F_2^n (exponent 4) with K = <e_0> and coordinate noise, SDP and val are >= 1 - delta but every free subgroup loses >= N delta (1-delta)^(N-1)
distinct_from:
  free-subgroup-rounding-is-universal-at-bounded-exponent: that is the universal statement this refutes; this is the explicit exponent-4 family with k = 2 that defeats it.
  galois-games-round-through-free-subgroups: that proves free-subgroup and permutable rounding as lower bounds on the value; this shows free subgroups can be far worse than the value when K is not normal.
---

**ESTABLISHED.** Let `N = 2^n`, `B = F_2^N` with coordinates indexed by
`F_2^n`, and `G = B x| F_2^n`, where `F_2^n` permutes coordinates by
translation. `G` has exponent `4`. Put `K = <e_0>`, a non-normal subgroup of
order `k = 2` whose conjugates are the `N` subgroups `<e_j>`. Let `mu_delta` be
the law of independent coordinate flips with probability `delta`, supported on
`B`. It is symmetric and conjugation-invariant.

1. `SDP Gal(G,K,mu_delta) >= 1 - delta` and `val Gal(G,K,mu_delta) >= 1 - delta`,
   through `L = { b in B : b_0 = 0 }`, which meets `K` trivially and permutes
   with it.
2. Every `H` acting freely on `G/K` contains no `e_j`, so
   `mu_delta(G \ H) >= N delta (1 - delta)^(N-1)`.
3. With `delta = eps = N^-2`, every free `H` has
   `mu(G \ H) >= (N - 1) eps log_2 k`. So no constant `C(4)` exists in
   `free-subgroup-rounding-is-universal-at-bounded-exponent`.

The value is not the issue: permutable rounding reaches `1 - delta`. What
fails is freeness, which asks `H` to avoid all `N` conjugates of `K`. Rounding
through inducing kernels pays exactly a factor `[G : N_G(K)]` (Theorem 14 of
the artifact, stated there for monomial certificates), and here that factor is
`N`. Whether the value itself rounds linearly for non-normal fibres at bounded
exponent is not settled here.

Artifact: `research/artifacts/ugc-rounding-normal-fibres-2026-09-13.md`,
Proposition 13.
