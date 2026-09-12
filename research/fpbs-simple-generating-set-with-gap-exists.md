---
rg: 2
id: fpbs-simple-generating-set-with-gap-exists
kind: claim
title: Every nonamenable group has a simple Cayley graph with strict thresholds
distinct_from:
  fpbs-benjamini-schramm-universal: that asserts strict thresholds on every Cayley graph; this asserts them on at least one simple Cayley graph.
  fpbs-nonuniqueness-phase-is-a-group-invariant: that asserts independence of the generating set; this asserts that one good generating set exists.
artifacts:
  - research/artifacts/fpbs/docs/benjamini-schramm-frontier-map.md
---

**OPEN.** Every nonamenable finitely generated group `Gamma` has a finite
symmetric generating set `S`, not containing the identity, whose simple Cayley
graph has `p_c(Cay(Gamma,S)) < p_u(Cay(Gamma,S))`.

This is the question of Juschenko--Nagnibeda, arXiv:1206.2183v3 (abstract, read
from the PDF on 2026-09-12). Pak--Smirnova-Nagnibeda, C. R. Acad. Sci. Paris 330
(2000) 495--500, prove the gap for the multiset powers `S^(k)` of `S ∪ {e}`.
That statement is quoted from Juschenko--Nagnibeda Theorem 4, since the paper is
not on arXiv. Those Cayley graphs have multiple edges, so it is not this claim.

## Attempts

* **Spectral radius below one half.** By Juschenko--Nagnibeda Proposition 3,
  credited to Pak--Smirnova-Nagnibeda, `rho(Gamma,S) < 1/2` implies `p_c < p_u`.
  Simple generating sets of small spectral radius are known in three cases:
  - groups containing `F_2` have them with `rho -> 0` (their page 4);
  - property RD gives `rho(S^k) -> 0` (their Proposition 7);
  - Juschenko--Nagnibeda prove the claim whenever `Gamma` contains a finitely
    generated subgroup with an infinite normal subgroup and nonamenable
    quotient. This covers the free Burnside groups `B(n,p)`, `n >= 2`,
    `p >= 665`.

  **Where it stops:** it misses a nonamenable group with no free subgroup and no
  such subgroup, for example a Tarski monster. Whether every nonamenable group
  has simple generating sets of arbitrarily small spectral radius is open.
* **Every-generating-set classes.** Acylindrically hyperbolic groups, and groups
  not of fixed price one, satisfy the claim through `fpbs-sc-choi-seo` and
  `fpbs-non-fixed-price-one-has-nonuniqueness`. **Where it stops:** monsters of
  fixed price one are in neither class.
