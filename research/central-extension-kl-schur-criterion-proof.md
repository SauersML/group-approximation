---
rg: 2
id: central-extension-kl-schur-criterion-proof
kind: route
title: Extend the multiplier over the adjunction and correct the lifted root by a divisible central element
target: central-extension-kl-schur-criterion
requires: [nonsingular-adjunction-never-enlarges-schur-multiplier]
artifacts:
  - research/artifacts/kl-schur-kernel-central-extensions-2026-09-11.md
---

Section S5 of the artifact. Push `alpha` into a divisible hull `D`.
Surjectivity of the Schur map makes `iota o alpha_H` descend to `H_2(X)`,
which is realized by a central extension `E~` of `X` by `D` restricting to
the pushout of `E`. Lift the root `tau`. `w` evaluates at the lift to a
central `d in D`, and replacing the lift by `c tau~` with `c^m = d^(-1)`
solves `w`. For the converse in (2), the centralized quotient is a central
extension of `X`. If `Z` survives there, its class pulls back to `alpha`,
so `alpha_H` factors through the Schur map.
