---
rg: 2
id: separated-small-pairing-noise-test-proof
kind: route
title: Random low-value rich source games plus a McDiarmid pairing decoder
target: separated-small-pairing-families-defeat-the-noise-test
requires: []
artifacts:
  - research/artifacts/unique-games-pairing-entropy-obstruction-2026-09-11.md
---

Complete proof in Sections 3--5 of the artifact.

The source game is complete bipartite, with pairings assigned cyclically so
every left vertex sees each pairing equally often. It fixes a random pair of
each pairing at each left vertex and uses random right relabelings that send
that pair to right label `0`. Its value bound combines a Chernoff bound on
pair loads (each pairing contains exactly one pair through a given label,
whatever the family) with Hoeffding plus a union bound over labelings.

The folded labeling reads the chosen coordinate of the decoded pairing. The
decoder takes the pairing with the largest agreement score. Its error is at
most `|P| exp(-N rho^4 delta_0^2/96)`, by McDiarmid with total squared
differences `12/N` and the separation margin `lambda delta_0/2`. On correct
decoding both queries read right coordinate `0` through three noise kernels,
so they agree with probability `1/m + (1-1/m) rho^3`.
