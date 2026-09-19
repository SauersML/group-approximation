---
rg: 2
id: non-hyperlinear-from-sp2g-llp
kind: route
title: LLP of the symplectic lattice's full C*-algebra makes Deligne's universal-cover lattice non-hyperlinear
target: non-hyperlinear-group
requires:
  - sp2g-z-full-c-star-algebra-has-llp
  - llp-implies-weak-ucp-stability
  - dogon-sp2g-weak-ucp-nonhyperlinear
---

Chain: LLP of `C^*(Sp_(2g)(Z))` gives weak ucp-stability of `Sp_(2g)(Z)`
(`llp-implies-weak-ucp-stability`), which by Dogon's Corollary 1.9
(`dogon-sp2g-weak-ucp-nonhyperlinear`) makes the Deligne universal-cover
lattice `Gamma~` non-hyperlinear.  The witness is a finitely generated
lattice in `Sp~_(2g)(R)`, non-residually finite by Deligne.

By the subgroup fence recorded in the hole, the hypothesis is only
possible at `g = 2`, so the route reads: **if `C^*(Sp_4(Z))` has the LLP,
the pullback of `Sp_4(Z)` to the universal cover of `Sp_4(R)` is a
non-hyperlinear lattice.**  This is the residually-finite corner of the
lifting square (`llp-non-rf-kazhdan-group-is-non-hyperlinear` is the
non-residually-finite corner); it consumes a lifting property where every
neighbouring route consumes a stability theorem, and its refutation
would extend Ioana--Spaas--Wiersma to all classical higher-rank lattices.
