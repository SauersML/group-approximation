---
rg: 2
id: finitary-split-extension-surjunctivity-proof
kind: route
title: Transplant to finite site quotients, peel stabilizer-coset strata, and close with the coset-region lemma
target: finitary-split-extension-surjunctivity-permanence
requires: []
artifacts:
  - research/artifacts/finitary-split-extension-surjunctivity-2026-09-11.md
  - research/artifacts/rf-lamp-wreath-surjunctivity-2026-09-11.md
---

Complete direct proof. The permutational wreath artifact supplies:

* Lemma 1.1: transplants of injective automata are injective.
* Lemma 1.2: separating transplants force surjectivity.
* Lemma 3.1: the coset-region lemma over a surjunctive subgroup.
* The peeling scheme of Proposition 4.1.

The finitary artifact checks that the axioms supply everything the scheme
uses:

* **Separation (A1).** The coset spaces `ker(q o p_S)\W ~= Q x G` separate
  finite subsets of `W`.
* **Strata and slices (A2).** The strata are finite unions of right cosets of
  point stabilizers, and away from the strata of `U\V` the transplant acts on
  left cosets of `Q_V` as the `V`-level transplant.
* **Invariance (A3).** The transplants commute with left translations by the
  stabilizer intersections `G_U`, which are surjunctive subgroups of `G`.

Standard background: Curtis--Hedlund--Lyndon over arbitrary groups, subgroup
heredity of surjunctivity, and compactness.
