---
rg: 2
id: one-relator-groups-satisfy-strong-atiyah
kind: claim
title: One-relator groups satisfy the Strong Atiyah conjecture over C (Jaikin-Zapirain--Lopez-Alvarez)
distinct_from:
  one-relator-groups-sofic: that is Pestov's open soficity question for the same class; this is an established L^2-integrality theorem for the class, proved without soficity through local indicability.
  nonsofic-one-relator-group: that asks for a nonsofic one-relator group; this says any such group would satisfy Strong Atiyah, which makes it a nonsofic Strong Atiyah group.
  strong-atiyah-passes-to-locally-indicable-extensions: that is the extension theorem of the same paper; this is its corollary for one-relator groups, which combines the locally indicable case with the virtually special case.
---

**ESTABLISHED (literature import)** by [[one-relator-groups-satisfy-strong-atiyah-citation]].

Every one-relator group `G` satisfies the Strong Atiyah conjecture over `C`:
the orders of its finite subgroups are bounded, and
`rk_G(A) in (1/lcm(G)) Z` for every matrix `A` over `C[G]`. For torsion-free
`G` the values are integers.

## Source

Jaikin-Zapirain and Lopez-Alvarez, arXiv:1810.12135v4, Math. Ann. 376 (2020),
read from the arXiv PDF on 2026-09-12, pages 2-3.

* **Corollary 1.3**, verbatim: "The strong Atiyah conjecture, the strong
  algebraic eigenvalue conjecture, the center conjecture and the independence
  conjecture hold for one-relator groups."
* **The printed derivation**, verbatim: "One-relator groups with torsion are
  virtually special by a theorem of D. Wise [35]. The strong Atiyah conjecture
  for virtually special groups over C is proved in [18]. Also virtually special
  groups are sofic. One-relator groups without torsion are locally indicable by
  a result of S. Brodskii [2]." The torsion-free case is Theorem 1.1: "Let G be
  a locally indicable group. Then G satisfies the strong Atiyah conjecture over
  C."
* **Not re-read:** Wise's theorem, Brodskii's theorem, and reference [18]
  (Jaikin-Zapirain, *The base change in the Atiyah and the Lueck approximation
  conjectures*).

## Consequence for nonsofic groups

By the printed derivation, a one-relator group with torsion is virtually
special, hence sofic. So a nonsofic one-relator group is torsion-free and
locally indicable, and it satisfies Strong Atiyah over `C` with integer values.
This is the route `nonsofic-atiyah-via-nonsofic-one-relator-group`.
