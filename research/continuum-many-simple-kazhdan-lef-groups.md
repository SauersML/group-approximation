---
rg: 2
id: continuum-many-simple-kazhdan-lef-groups
kind: claim
title: For every prime power q there are continuum many pairwise non-isomorphic infinite finitely generated simple Kazhdan groups that are LEF (hence sofic and hyperlinear)
distinct_from:
  kazhdan-hyperbolic-continuum-non-fng-maximal-kernels: that gives continuum many simple torsion-free Kazhdan quotients of a hyperbolic group, not known to be sofic; this gives continuum many simple Kazhdan groups that are LEF, hence sofic and hyperlinear.
  continuum-nonisomorphic-fg-non-mf: that is a continuum of non-MF groups; this is a continuum of simple LEF (hence MF) Kazhdan groups, on the opposite side of the approximation dichotomy.
  simple-kazhdan-lef-group-from-minimal-subshift: that proves each S_X is infinite simple Kazhdan LEF; this shows the S_X realize continuum many isomorphism types.
  subshift-elementary-group-word-problem-degree: that (2026-09-12, reviewed PASS in research/artifacts/ex-review-groups-2026-09-12-part11.md §11.4) already obtains uncountably many isomorphism classes of these subshift groups through Turing degrees, and its artifact gives WP(S_X) ≡_T L(X); this gives an independent counting proof through markings.
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

**Review (un-verify-open, 2026-09-13, `research/artifacts/un-review-open-2026-09-13-part1.md` §1.2): PASS, subsumed
in substance.** The countable-fibre argument (injective `X ↦ φ(σ_X) ∈ H^I`, `H` countable) and the continuum
count were re-derived. The conclusion is already on main through `subshift-elementary-group-word-problem-degree`
(Turing degrees of `WP(S_X)` separate continuum many classes); the counting proof is the new part.
