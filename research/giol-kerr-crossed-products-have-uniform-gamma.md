---
rg: 2
id: giol-kerr-crossed-products-have-uniform-gamma
kind: claim
title: The non-Z-stable Giol-Kerr crossed products have uniform property Gamma
root: true
artifacts:
  - research/artifacts/stw99-dynamics-cluster-2026-08-30.md
---

The Giol--Kerr free minimal `Z`-actions with non-`Z`-stable crossed
products (Crelle 2010) yield algebras with uniform property Gamma, even
though the inclusion `(C(X) subset C(X) rtimes Z)` fails relative uniform
Gamma and the algebra fails strict comparison. STW record the question as
open; it is the natural absolute-versus-relative separation candidate.

**Established (2026-09-12)** through `giol-kerr-uniform-gamma-vaccaro-citation`.
Vaccaro, arXiv:2604.24682v2, Theorem A(2): crossed products of free minimal
actions of countably infinite FC groups on compact metric spaces have uniform
property Gamma.  Minimal homeomorphisms of infinite compact spaces are free,
and `Z` is FC.  So absolute uniform Gamma holds here while the Cartan-relative
version fails, which separates the two on a natural example.  By CETW Theorem A
(`uniform-gamma-algebras-satisfy-toms-winter`) this also gives a second reason
why these non-Z-stable algebras fail strict comparison.

## Attempts

- Conditional route recorded:
  `giol-kerr-uniform-gamma-via-tracial-completion` derives this from
  Problem XXXV plus the now-established Problem XX (Vaccaro).
- Direct route: `giol-kerr-flat-name-local-colourings-give-uniform-gamma`
  reduces the root to one finite-stage statement,
  `giol-kerr-return-towers-admit-flat-name-local-colourings`. It asks for
  continuous off-diagonal tower projections that are simultaneously flat,
  local for finite orbit names, compatible with recursive boundary maps, and
  compatible with the return successor.
- Fixed Fourier colourings fail name-locality, while pointwise name
  clustering is discontinuous at collision strata. Positive mean dimension
  rules out Cartan-relative Gamma but does not rule out these off-diagonal
  projections.
- Vaccaro's method (stable rank one plus tracial local homogeneity gives
  uniform Gamma) covers the AH stable-rank-one setting.  An earlier version
  of this note judged the Giol--Kerr case unverified.  It is covered by
  Vaccaro's crossed-product theorem.  That theorem uses Niu's tracial local
  homogeneity for actions with the uniform Rokhlin property, not stable rank
  one, and Naryshkin supplies the uniform Rokhlin property for FC groups.
