---
rg: 2
id: binary-lcs-gap-from-central-leavitt-seed
kind: route
title: Embed the specified six-generator Leavitt sign seed into a finite linear-system solution group
target: binary-lcs-perfect-qc-strict-qa-gap-exists
requires:
  - leavitt-central-sign-seed-for-lcs
  - slofstra-solution-group-embedding-preserves-marked-involutions
  - marked-approximate-radical-survives-solution-group-embedding
  - lcs-tracial-ru-gap-equiv-nonhyperlinear
artifacts:
  - research/artifacts/liu-to-linear-games-and-marked-gap-2026-09-20.md
---

The seed supplies a particular finitely presented group K and a nontrivial
central involution J killed in every tracial matrix model. Slofstra's
effective theorem embeds K in a finite binary solution group while
preserving J. Injectivity keeps the output sign nontrivial; restriction
through the fixed embedding words kills it in all approximate models, by
the third premise. Paddock--Slofstra Lemma 5.7 and Theorem 3.11 then give
the tracial/non-R^U and perfect-qc/strict-qa conclusions. Compactness for a
fixed full-support question law supplies a positive gap as in the artifact.

This alternate route uses the concrete reviewed Thompson--Steinberg
presentation rather than Khanh's abstract finite-presentability theorem.
It still uses Jihao Liu's analytic input through the source radical theorem,
with Andreas Thom's conditional normalization contribution explicitly
retained. It is an effective construction specification, not a claim that
the final binary matrix and numeric gap have been emitted.
