---
rg: 2
id: continuum-many-simple-kazhdan-lef-groups
kind: claim
title: For every prime power q there are continuum many pairwise non-isomorphic infinite finitely generated simple Kazhdan groups that are LEF (hence sofic and hyperlinear)
distinct_from:
  kazhdan-hyperbolic-continuum-non-fng-maximal-kernels: that gives continuum many simple torsion-free Kazhdan quotients of a hyperbolic group, not known to be sofic; this gives continuum many simple Kazhdan groups that are LEF, hence sofic and hyperlinear.
  continuum-nonisomorphic-fg-non-mf: that is a continuum of non-MF groups; this is a continuum of simple LEF (hence MF) Kazhdan groups, on the opposite side of the approximation dichotomy.
  simple-kazhdan-lef-group-from-minimal-subshift: that proves each S_X is infinite simple Kazhdan LEF; this shows the S_X realize continuum many isomorphism types.
artifacts:
  - research/artifacts/un-open-5-marked-subshift-groups-2026-09-13.md
---

For every prime power `q`, there are continuum many pairwise non-isomorphic groups `S` such that `S` is infinite,
finitely generated, simple, has property (T), is LEF (hence sofic and hyperlinear), and has no nontrivial finite
quotient.

Witnesses: `S_X = EL_3(LC(X,F_q) ⋊ Z)/Z` for infinite minimal subshifts `X ⊆ {0,1}^Z`, e.g. the Sturmian
subshifts `X_α`. Every isomorphism class contains at most countably many `S_X`. Before 2026-09-12 no infinite
simple Kazhdan group was known to be sofic (`infinite-simple-kazhdan-hyperlinear-group`). This turns that one
example into a continuum of isomorphism types.

Not claimed: which pairs `S_X, S_Y` are isomorphic. See `subshift-elementary-group-isomorphism-forces-orbit-equivalence`.
