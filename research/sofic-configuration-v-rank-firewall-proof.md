---
rg: 2
id: sofic-configuration-v-rank-firewall-proof
kind: route
title: Ultraproduct permutation-module ranks along a sofic approximation satisfy every confined premise and have the sofic values
target: sofic-configurations-cannot-force-v-rank-triviality
requires: []
artifacts:
  - research/artifacts/thompson-v-rank-gate-sofic-and-characteristic-firewalls-2026-09-12.md
---

Artifact Sections 1 and 2.

1. **Rank function** (Lemma 1.1). Extend a sofic approximation `sigma_k : K -> Sym(n_k)` linearly and entrywise.
   Put `rk_K(M) = lim_omega rank(sigma_k(M))/n_k`.
   - (S0), (S2) and (S3) hold at every stage.
   - (S1) holds in the limit, since the multiplicativity defect of a finite combination has normalized rank at most
     the sum of its Hamming defects.
2. **Values** (Lemma 1.1).
   - Asymptotic freeness forces almost every point onto `sigma_k(g)`-cycles of length exactly `ord(g)`, or of
     unbounded length when `g` has infinite order.
   - On an `n`-cycle, `q(C_n)` is multiplication by `q` on `F[t]/(t^n - 1)`, with kernel dimension
     `deg gcd(q, t^n - 1)`.
3. **Inertness** (Theorem 1.2).
   - The Sylvester premises and ring identities hold for `rk_K`.
   - Single-element conjugacy data hold because the values depend only on `q` and `ord(g)`.
   - The conclusions fail by Lemma 1.1.
4. **Instances** (Proposition 2.1 and Section 2.2).
   - With `x` having a wandering clopen `W` and `L <= Rist_V(W)`, the conjugates `x^j L x^(-j)` have disjoint
     supports. `<x>` meets their direct sum trivially, so `<x, L> ≅ L wr Z`. This is amenable for amenable `L`.
   - Free products of finite groups are residually finite (Gruenberg, standard), hence sofic.

Imports at statement level: Hayes–Sale, only for sofic non-amenable lamps `L`; Gruenberg's residual finiteness of
free products of finite groups.
