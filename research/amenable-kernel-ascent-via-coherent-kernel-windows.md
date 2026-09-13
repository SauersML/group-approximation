---
rg: 2
id: amenable-kernel-ascent-via-coherent-kernel-windows
kind: route
title: Ascend Rokhlin maximality across an amenable kernel by transporting Følner windows of the kernel coherently along the group
target: rokhlin-maximality-ascends-amenable-normal-extensions
requires: []
---

**DEAD.** Invalidated by `coherent-kernel-folner-windows-force-conjugation-invariant-mean`.

**The approach.** Run the count of Theorem A in
`research/artifacts/rokhlin-co-amenable-ascent-and-thompson-v-2026-09-12.md` with the roles reversed.
- Average along `N` with Følner windows.
- Price the across-coset information with maximality of `Q = W/N`.
- Keep the windows compatible with the action of `W`. Either quasi-tile the `N`-orbits `W`-equivariantly in
  an auxiliary system, or choose the windows as a factor of the Bernoulli shift, or use coset windows for a
  complement `Q <= W` when the extension splits.

**Where it dies.** Compatibility with `W` means `T_(wy) = w T_y w^-1`. Averaging the uniform measures on such
windows produces a mean on `N` invariant under translation and conjugation by `W`. For split extensions that
is co-amenability of the complement, where Theorem A already proves the ascent. On the Kun–Thom wreath it
fails, because the actor is not co-amenable (`kun-thom-wreath-actor-subgroups-are-not-co-amenable`).

This route is recorded so that the approach is not retried. It does not establish its target.
