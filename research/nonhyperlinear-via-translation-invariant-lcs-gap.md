---
rg: 2
id: nonhyperlinear-via-translation-invariant-lcs-gap
kind: route
title: A nonhyperlinear group from a translation-invariant linear rule with a torus-uniform gap
requires:
  - translation-invariant-lcs-torus-gap-forces-nonhyperlinear
  - translation-invariant-lcs-with-uniform-torus-gap-exists
target: non-hyperlinear-group
---

If some translation-invariant binary linear rule \(R\) on \(\mathbb Z^2\) has
\(J\ne1\) in its solution group and a torus-uniform almost-model gap
(`translation-invariant-lcs-with-uniform-torus-gap-exists`, OPEN), then
`translation-invariant-lcs-torus-gap-forces-nonhyperlinear` makes the finitely
presented group \(\mathrm{Sol}_R\rtimes\mathbb Z^2\) nonhyperlinear.

This is the quantum-tiling route of `research/artifacts/ideas-2026-09-13/nh/nh-games.md`
(approach 4), with the averaging step now proved: almost-models periodize onto
tori. The remaining hypothesis needs an analytic rigidity input (see the
Attempts of the open node).
