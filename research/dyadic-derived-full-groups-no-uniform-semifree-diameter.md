---
rg: 2
id: dyadic-derived-full-groups-no-uniform-semifree-diameter
kind: claim
title: If an infinite minimal subshift has constant dyadic towers with bounded induced alphabets, its derived topological full group has no uniform semi-free diameter
artifacts:
  - research/artifacts/sk-rauzy-intermediate-2026-09-14-part1.md
distinct_from:
  dyadic-tower-subshift-full-group-non-uniform-growth: that is the growth clause of Cornulier's question 7 (ω([[T]]′) = 1); this is its semi-free-diameter clause, derived from it.
  dyadic-substitution-derived-full-groups-non-uniform-growth: that is the growth clause for dyadic substitution subshifts; this is the semi-free-diameter clause for the wider tower class.
---

**ESTABLISHED (unreviewed; sk-rauzy-intermediate).**
- **Statement.** Let `(X,T)` satisfy the hypotheses of `dyadic-tower-subshift-full-group-non-uniform-growth`: (H1) and (H2) at infinitely many scales. An example is every primitive substitution of constant length 2 with a non-periodic fixed point. Then for every `N ≥ 1` there is a finite generating set of `[[T]]′` whose `N`-ball contains no pair of elements freely generating a free semigroup.
- **Meaning.** The semi-free clause of Cornulier's question 7 (Bourbaki 1064, arXiv:2002.09342, source l.216) has a negative answer for these subshifts. Verbatim: "existe-t-il un entier $N$ tel que pour tout système générateur, la $N$-boule contient un couple d'éléments engendrant librement un semi-groupe libre".
- **Not covered.** The torsion-free clause ("resp. contient un élément sans torsion") stays open. The generating sets of the dyadic proof contain the shift pair `σ_n`, which has infinite order.

Route: `dyadic-derived-full-groups-no-uniform-semifree-diameter-proof`.
