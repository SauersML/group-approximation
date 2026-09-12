---
rg: 2
id: pullback-smoothness-pairing-count-proof
kind: route
title: Count the support of the pull-back distribution against the density ceiling
target: pullback-smoothness-needs-exponentially-many-pairings
requires: []
artifacts:
  - research/artifacts/unique-games-pairing-entropy-obstruction-2026-09-11.md
---

Theorem 2 of the obstruction artifact, Section 7.

The pull-back distribution is supported on the union of the `|F|` sets of
pair-constant vectors, each of size `m^n`. A set of mass at least `theta` on
which the density is at most `C m^(-2n)` has at least `theta m^(2n)/C` points
in that support. Hence `|F| m^n >= theta m^(2n)/C`.

The mass of the balanced set is family independent, because pull-back doubles
every symbol count.
