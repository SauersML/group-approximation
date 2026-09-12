---
rg: 2
id: tester-host-pos-iff-maximal-bernoulli-rokhlin-entropy-proof
kind: route
title: Embed the square of the universal host in itself and apply the self-copy dichotomy
target: tester-host-pos-iff-maximal-bernoulli-rokhlin-entropy
requires:
  - whitehead-universal-finitely-presented-container
  - rokhlin-supremum-dichotomy-with-centralized-self-copies
  - positive-rokhlin-entropy-action-gives-positive-supremum
  - seward-per-group-rokhlin-entropy-of-bernoulli-shifts
artifacts:
  - research/artifacts/rokhlin-entropy-self-copy-dichotomy-2026-09-12.md
---

Section 3 of the artifact.

* **Hypotheses.** The container theorem embeds every countably generated recursively presented group in `U`, in particular the finitely presented group `U x U`. Also `Tord(U) = {2,3,4,...}`. The first factor `G` and a cyclic subgroup `T_n` of order `n` in the second factor commute and meet trivially.
* **Dichotomy.** The self-copy corollary gives `h_sup(U)` equal to `0` or `infinity`.
  * POS(`U`) gives `h_sup(U) > 0` by Seward's Corollary 7.7, hence INF(`U`).
  * INF(`U`) gives RBS(`U`) by Seward's per-group formulas.
  * RBS(`U`) gives POS(`U`) through the Bernoulli 2-shift.
* **Down-passing.** Restrict the Bernoulli 2-shift over `U` to an infinite subgroup `K`. The restriction is free and mixing, and `h^Rok_K >= h^Rok_U = log 2`, because a generating partition for `K` also generates for `U`.
