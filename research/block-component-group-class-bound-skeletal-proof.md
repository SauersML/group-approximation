---
rg: 2
id: block-component-group-class-bound-skeletal-proof
kind: route
title: The skeletal filtration is central, commutators vanish below twice the rank, and the top skeleton ends the series
target: block-component-group-class-at-most-excess-plus-two
requires:
  - u2-triple-samelson-class-three-stage
artifacts:
  - research/artifacts/component-group-class-bound-by-excess-2026-09-12.md
---

Let F_k be the kernel of restriction to the (k−1)-skeleton. Then
F_1 = Pi(E), because U(r) is connected, and F_{d+1} = 1.

Centrality: [Pi(E), F_k] ⊆ F_{k+1}. Make n identically 1 on X^{(k−1)}. On
each k-cell, shrink its support to a small interior ball B. On B, deform g to
the constant g(center), keeping the commutator 1 near ∂B. Conjugating by a
constant in the connected group U(r) is homotopic to the identity rel ∂B, so
[g, n] is trivial on X^{(k)}.

Depth: Pi(E) -> K^1(X) is a homomorphism to an abelian group, so gamma_2 lies
in its kernel N. Below twice the rank, the gauge fibration
G(F) -> G(F (+) 1) -> S(F (+) 1) has a fibre sphere of dimension above
dim + 1. So stabilization is an isomorphism on pi_0, and
Pi(E|X^{(2r−1)}) ≅ K^1(X^{(2r−1)}). Naturality then gives N ⊆ F_{2r}.

Count: gamma_c ⊆ F_{2r+c−2}, which is trivial once c >= d − 2r + 3.

Limits: stage groups inject modulo U_0 (Toms arXiv:2609.09535v1, Lemma 7.1)
and exhaust by polar approximation, and gamma_c commutes with direct limits.
Every finitely generated subgroup lives at one stage, which gives local
nilpotency.

The exact class three of C(T^2 x S^3, M_2) combines this bound (d = 5, r = 2)
with the prerequisite's nonzero triple commutator.
