---
rg: 2
id: torus-automata-over-rf-or-domain-groups-are-surjunctive
kind: claim
title: Injective continuous equivariant self-maps of torus full shifts are surjective over residually finite groups, and on the circle alphabet over every group whose rational group ring is a domain
distinct_from:
  torus-automata-with-regular-degree-are-surjective: that is the degree lemma, with no injectivity hypothesis; this proves the regularity input from injectivity via invariance of domain on periodic tori, in two cases.
  kaplansky-zero-divisor-conjecture: that is the ring-theoretic conjecture; this uses its conclusion for Q[G] as a hypothesis and derives circle-alphabet surjunctivity from it.
artifacts:
  - research/artifacts/torus-alphabet-degree-2026-09-17.md
---

Let `tau` be an injective continuous `G`-equivariant self-map of `(T^d)^G`, with degree
matrix `D in M_d(Z[G])` as in `torus-automata-with-regular-degree-are-surjective`.

**Periodic-point lemma.** For every finite-index normal `N <= G`, right multiplication by
`p_N(D)` is invertible on `Z[G/N]^d`. In particular `epsilon(D) in GL_d(Z)`.

**Claim.**
- (a) If `G` is residually finite, `tau` is surjective, for every `d`.
- (b) If `Q[G]` has no zero divisors and `d = 1`, `tau` is surjective.

Case (b) needs no approximation of `G`. By the standard leading-term argument it covers
unique-product groups, including every left-orderable group, and every group satisfying
Kaplansky's zero-divisor conjecture over `Q`, regardless of whether the group is sofic.

**ESTABLISHED 2026-09-17** by
[[torus-automata-over-rf-or-domain-groups-are-surjunctive-proof]].

## Attempts

- 2026-09-17 (swarm-0917-w4-gs-decomp-new): Section 2 of the artifact.
  - `tau` maps `Fix(N) = (T^d)^(G/N)` into itself.
  - Injectivity plus invariance of domain makes the restriction a homeomorphism of a
    closed torus, whose `H^1` matrix is `p_N(D)`.
  - Residual finiteness detects any kernel vector in a finite quotient (case a). For
    `d = 1`, `epsilon(D) = +-1` gives `D != 0` (case b).
- Where (b) stops. Over `Z/2 x Z/3`, `D = s + s^2 - t` has `epsilon(D) = 1` but
  `(1-t)(1-s) D = 0`. So groups with torsion need more than the constants, and so does
  `d >= 2`. See `injective-torus-automata-have-regular-degree`.
