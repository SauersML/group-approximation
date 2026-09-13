---
rg: 2
id: primitive-binary-words-give-four-regular-simple-expanders
kind: claim
title: Every primitive binary word gives a four-regular finite simple Cayley expander with one absolute spectral gap
distinct_from:
  finite-simple-groups-converge-to-simple-kazhdan-group: that gives bounded degree and expansion along minimal-subshift approximants; this gives degree four and a uniform absolute spectral bound for every primitive binary cyclic word.
artifacts:
  - research/artifacts/pestov91-four-regular-expanders-and-limits-2026-09-13.md
---

For every primitive binary cyclic word `z` of length `N>=2`, substitute
the cyclic permutation `P` and diagonal letter indicator `D` into the
three-generator formulas for `(c,t,w)`. They generate `SL_(3N)(F_2)`
and have orders `7,2,2`. The Cayley graph for `{c,c^{-1},t,w}` is simple,
connected and four-regular.

There is a single `kappa>0` independent of `z,N` such that the normalized
adjacency spectrum off the constants lies in
`[-(1+cos(pi/7))/2, 1-kappa^2/8]`. Thus the entire family has one positive
absolute spectral gap. The constant `kappa` comes from the fixed
unit-idempotent Kazhdan source; no numerical value is asserted.
