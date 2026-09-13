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
  - research/artifacts/jn-simple-gap-via-thom-2026-09-12.md
---

**ESTABLISHED (literature import)** by
`fpbs-simple-generating-set-with-gap-exists-citation`. Every nonamenable finitely
generated group `Gamma` has a finite symmetric generating set `S`, not containing
the identity, whose simple Cayley graph has `p_c(Cay(Gamma,S)) < p_u(Cay(Gamma,S))`.

The theorem is Thom's. A. Thom, *A remark about the spectral radius*,
arXiv:1306.1767 (2013), Theorem 1, gives finite symmetric generating sets with
`rho(S) < epsilon` for every `epsilon > 0`. His Corollary 8 states the percolation
consequence. The step from `rho < 1/2` to `p_c < p_u` is due to
Pak--Smirnova-Nagnibeda, C. R. Acad. Sci. Paris 330 (2000) 495--500. It rests on
Benjamini--Schramm, Electron. Comm. Probab. 1 (1996) 71--82. Both statements are
quoted from Juschenko--Nagnibeda, arXiv:1206.2183v3, p.3.

The question was posed as Juschenko--Nagnibeda Question 6(1), p.4. On p.4 they say
"simple" means a Cayley graph without loops or multiple edges. Their v3, p.6, says
Thom answered it.

Nothing here is new. The route adds one elementary step: deleting the identity
from Thom's set keeps `rho <= 1/3`, so the graph has no loops.

Not claimed.
- `p_c < p_u` on every Cayley graph. `fpbs-benjamini-schramm-universal` stays open.
- That the non-uniqueness phase does not depend on the generating set.
  `fpbs-nonuniqueness-phase-is-a-group-invariant` stays open.
- Juschenko--Nagnibeda Questions 6(2) and 6(3), about the powers `S^k`. Thom's
  `S_k` is a subset of `Sigma^k`, not all of `Sigma^k`.

## Partial results before Thom

The import supersedes these; they are kept as history.
* **Spectral radius below one half, special classes.** Juschenko--Nagnibeda list
  three cases with simple generating sets of spectral radius tending to 0:
  - groups containing `F_2` (p.4, observed by Pak--Smirnova-Nagnibeda);
  - property RD, which gives `rho(S^k) -> 0` (Proposition 7);
  - groups containing a finitely generated subgroup with an infinite normal
    subgroup and nonamenable quotient. This covers the free Burnside groups
    `B(n,p)`, `n >= 2`, `p >= 665` (their Section 2).

  These classes do not obviously cover every nonamenable group. Thom's Theorem 1
  needs nothing beyond nonamenability.
* **Every-generating-set classes.** Acylindrically hyperbolic groups, and groups
  not of fixed price one, have `p_c < p_u` on every Cayley graph, through
  `fpbs-sc-choi-seo` and `fpbs-non-fixed-price-one-has-nonuniqueness`. Monsters
  of fixed price one are in neither class.
