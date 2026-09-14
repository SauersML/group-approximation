---
rg: 2
id: pullback-smoothness-needs-exponentially-many-pairings
kind: claim
title: The pull-back density comparison in the Rich 2-to-1 analysis needs at least about m^n pairings
invalidates:
  - smooth-design-hardness-via-subexponential-families
distinct_from:
  separated-small-pairing-families-defeat-the-noise-test: that shows the test itself fails on separated subexponential families; this is a counting lower bound on any family admitting the density comparison of BKM Lemma 4.2, separated or not.
artifacts:
  - research/artifacts/unique-games-pairing-entropy-obstruction-2026-09-11.md
  - research/artifacts/unique-games-smooth-design-richness-2026-09-11.md
---

**ESTABLISHED.** For a family `F` of perfect pairings of `[2n]` and `m >= 2`, let
`nu_(F,m)` be the law of `z = p_pi^(-1)(x)`, with `pi` uniform in `F` and `x`
uniform in `[m]^n`.

If `nu_(F,m)(E) >= theta` and `nu_(F,m)(z) <= C m^(-2n)` for every `z in E`, then
`|F| >= theta m^n / C`: the support of `nu_(F,m)` has at most `|F| m^n` points.

The count of each symbol in `p_pi^(-1)(x)` is twice its count in `x`, for every
`pi`. So the set of `K`-roughly balanced points has mass `1 - 2^(-Omega(K))`
for every family. The comparison BKM prove for all pairings (ECCC TR19-141,
Lemma 4.2), and use in Lemma 4.12, therefore forces
`|F| >= (1 - 2^(-Omega(K))) m^n / C(K,m)`.
