---
rg: 2
id: normalizing-invariant-output-descends-to-quotient-proof
kind: route
title: Restrict to right-invariant configurations and read them on the quotient group
target: normalizing-invariant-output-descends-to-quotient
requires: []
artifacts:
  - research/artifacts/invariant-output-descent-and-sensitivity-2026-09-12.md
---

Restrict `tau` to one left `K`-coset. Right-`H`-invariant configurations on `K`
are functions on `K/H`, and for them `tau(x)(k) = f((xbar(kH . mH))_m)` because
`H` is normal in `K`. That is an automaton over `K/H`, injective since `tau` is.
The inclusion of invariant configurations in all configurations is proper, and
`tau` is injective with invariant output. So the image of the invariant
configurations is a proper subset of the invariant configurations, and the
quotient automaton is not surjective. Section 2 of the artifact.
