---
rg: 2
id: torus-automata-over-rf-or-domain-groups-are-surjunctive-proof
kind: route
title: Invariance of domain on the periodic tori pins the degree matrix in every finite quotient, then the degree lemma gives surjectivity
target: torus-automata-over-rf-or-domain-groups-are-surjunctive
requires:
  - torus-automata-with-regular-degree-are-surjective
artifacts:
  - research/artifacts/torus-alphabet-degree-2026-09-17.md
---

Section 2 of the artifact (Lemma 2 and Theorem 3).

1. **The periodic torus.** `Fix(N)` is homeomorphic to `(T^d)^(G/N)`, a closed connected
   manifold, and `tau` preserves it by equivariance.
2. **Invariance of domain.** The restriction `tau_N` is injective, so its image is open,
   closed and connected, and `tau_N` is a homeomorphism. Hence `tau_N^*` is invertible.
3. **Its matrix.** The inclusion `Fix(N) -> (T^d)^G` acts on `H^1` as `p_N`. So
   `tau_N^* (p_N xi) = p_N(xi) p_N(D)`, and right multiplication by `p_N(D)` is invertible
   on `Z[G/N]^d`. The case `N = G` gives `epsilon(D) in GL_d(Z)`.
4. **Case (a).** Suppose `0 != xi in Z[G]^d` with `xi D = 0`. Pick `N` with `p_N`
   injective on `supp xi`. Then `p_N(xi) != 0` and `p_N(xi) p_N(D) = 0`, contradicting
   step 3. So `D` is regular over `Q[G]`, and the degree lemma applies.
5. **Case (b).** `epsilon(D) = +-1` forces `D != 0`. In a domain `D` is then regular, and
   the degree lemma applies.
