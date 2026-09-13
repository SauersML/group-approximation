---
rg: 2
id: labbe-lef-via-periodic-quantum-tilings
kind: route
title: Periodic quantum tilings of Labbé's tiles at every scale would make its derived full group LEF
target: labbe-shift-derived-full-group-is-lef
requires:
  - z2-sft-derived-full-group-lef-from-tiling-modules
  - labbe-tiles-admit-periodic-quantum-tilings-at-every-scale
  - minimal-aperiodic-wang-shift-exists
artifacts:
  - research/artifacts/labbe-periodic-quantum-tilings-obstruct-fp-2026-09-13.md
---

1. **Setting.** `Omega_U` is a free minimal nearest-neighbour SFT (`minimal-aperiodic-wang-shift-exists`).
2. **Modules at every scale.** `labbe-tiles-admit-periodic-quantum-tilings-at-every-scale` gives, for
   each `D`, a nonzero `Λ`-periodic family on a finite-dimensional `W`. Corollary 2 of the artifact
   turns it into a nonzero finite-dimensional `A_D(Omega_U, k)`-module on `W ⊗ k[Z^2/Λ]`.
3. **LEF.** `z2-sft-derived-full-group-lef-from-tiling-modules` then makes `D([[Omega_U]])` LEF.

**Relation to the fp route.** This route implies `labbe-not-fp-via-periodic-quantum-tilings`, since LEF
already excludes finite presentation (`labbe-not-fp-via-lef`).

**No false establishment.** The second requirement is OPEN, so this route does not fire.
