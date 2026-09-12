---
rg: 2
id: non-hyperlinear-from-sp2g-flexible-hs-stability
kind: route
title: Flexible HS-stability of Sp_2g(Z) makes Deligne's universal-cover lattice non-hyperlinear
target: non-hyperlinear-group
requires:
  - sp2g-z-flexibly-hs-stable
  - kazhdan-weak-ucp-stability-is-flexible-stability
  - dogon-sp2g-weak-ucp-nonhyperlinear
---

Chain.
1. `sp2g-z-flexibly-hs-stable`: some `Sp_(2g)(Z)`, `g >= 2`, is flexibly
   HS-stable.
2. Flexible HS-stability implies weak ucp-stability, the immediate direction
   of `kazhdan-weak-ucp-stability-is-flexible-stability`.
3. Dogon Corollary 1.9 (`dogon-sp2g-weak-ucp-nonhyperlinear`): the pullback
   `Gamma~` of `Sp_(2g)(Z)` to the universal cover of `Sp_(2g)(R)` is not
   hyperlinear.

The witness `Gamma~` is Deligne's finitely generated, non-residually-finite
lattice.  Unlike `non-hyperlinear-from-sp2g-llp`, this route is not confined
to `g = 2`: failure of LLP for `g >= 3` does not bear on stability.  Its
open input carries the twisted-sector obstruction recorded in
`sp2g-flexible-stability-forces-twisted-non-ce`.
