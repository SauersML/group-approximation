---
rg: 2
id: labbe-shift-escapes-known-obstructions-proof
kind: route
title: Minimality gives full-support measures and aperiodicity blinds the finite-orbit obstructions
target: labbe-shift-derived-full-group-escapes-known-obstructions
requires:
  - minimal-aperiodic-wang-shift-exists
  - minimal-z2-subshift-derived-full-groups-are-fg-simple
  - sfts-without-finite-orbits-are-not-residually-finite-actions
artifacts:
  - research/artifacts/fp-simple-amenable-z2-sft-2026-09-12.md
---

## Why sufficient

1. **Finite generation and simplicity.** `Omega_U` is an infinite minimal subshift of `U^{Z^2}` with a free action (`minimal-aperiodic-wang-shift-exists`). `minimal-z2-subshift-derived-full-groups-are-fg-simple` then makes `D([[Z^2 ~ Omega_U]])` finitely generated, infinite and simple.
2. **Not compressible.** `Z^2` is amenable, so `Omega_U` carries an invariant Borel probability `mu`. Its support is closed, invariant and nonempty, hence everything by minimality. Suppose a clopen `A` contained disjoint clopen `B` and `C` with compact open bisections `A -> B` and `A -> C`. Then `mu(A) >= mu(B) + mu(C) = 2 mu(A)`, so `mu(A) = 0`, which contradicts full support. So the hypothesis of Corollary 1.2 in `amenable-full-group-forces-invariant-measure` fails.
3. **Extension theorem vacuous.** `Omega_U` is an SFT containing itself and invariant under every element of its full group. So the SFT neighbourhood in `fp-subshift-full-group-subgroups-extend-to-sft` may be `Omega_U` itself, which has no finite orbit, and the finite-orbit clause says nothing.
4. **Periodic points blind.** `Omega_U` is an SFT with no finite orbit. By `sfts-without-finite-orbits-are-not-residually-finite-actions` it has no periodic approximations and its action is not residually finite. So the hypotheses of `periodic-approximable-subshifts-host-no-fp-simple-group` item 1 and of Ma's Theorem C fail.
