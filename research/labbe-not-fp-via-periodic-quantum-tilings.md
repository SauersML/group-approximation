---
rg: 2
id: labbe-not-fp-via-periodic-quantum-tilings
kind: route
title: Periodic quantum tilings of Labbé's tiles at every scale would refute finite presentation of its derived full group
target: labbe-shift-derived-full-group-is-not-finitely-presented
requires:
  - zd-derived-full-group-fp-excludes-periodic-quantum-tilings
  - labbe-tiles-admit-periodic-quantum-tilings-at-every-scale
  - minimal-aperiodic-wang-shift-exists
artifacts:
  - research/artifacts/labbe-periodic-quantum-tilings-obstruct-fp-2026-09-13.md
---

1. **Setting.** `Omega_U` is a free minimal nearest-neighbour SFT (`minimal-aperiodic-wang-shift-exists`),
   so `zd-derived-full-group-fp-excludes-periodic-quantum-tilings` applies to it.
2. **Suppose** `D([[Omega_U]])` is finitely presented. That claim gives `D_0` such that `A_D(Omega_U, k)`
   has no nonzero finite-dimensional module for `D >= D_0` and every field `k`.
3. **A module.** `labbe-tiles-admit-periodic-quantum-tilings-at-every-scale` gives a nonzero
   `Λ`-periodic family on a finite-dimensional `W` at scale `D_0`. On `W ⊗ k[Z^2/Λ]` it defines a
   nonzero finite-dimensional `A_(D_0)`-module (artifact, Corollary 2).
4. **Contradiction.** So `D([[Omega_U]])` is not finitely presented.

**No false establishment.** The second requirement is OPEN, so this route does not fire.
