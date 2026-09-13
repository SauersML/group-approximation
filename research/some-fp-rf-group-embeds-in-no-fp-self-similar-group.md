---
rg: 2
id: some-fp-rf-group-embeds-in-no-fp-self-similar-group
kind: claim
title: Some finitely presented residually finite group embeds in no finitely presented self-similar group
refuted_by:
  - every-fp-rf-group-embeds-in-fp-self-similar-group
distinct_from:
  every-fp-rf-group-embeds-in-fp-self-similar-group: that is the universal embedding statement; this is exactly its negation, recorded as the positive answer to the second part of Zaremsky Problem 3.9.
  some-fp-rf-group-acts-on-no-regular-rooted-tree: that asserts a finitely presented residually finite group with no faithful action on any regular rooted tree, which excludes every self-similar host; this only excludes finitely presented self-similar hosts, and is implied by that claim.
---

**OPEN.** There is a finitely presented residually finite group `G` such that
no finitely presented self-similar group `H <= Aut(T_d)`, for any `d >= 2`,
contains a copy of `G`.

This is the negation of `every-fp-rf-group-embeds-in-fp-self-similar-group`,
and it is the positive answer to the second part of Zaremsky Problem 3.9 in its
strongest reading (see `zaremsky-3-09-braid-groups-self-similar`).

**Sufficient mechanism.** `some-fp-rf-group-acts-on-no-regular-rooted-tree`,
through the route `fp-rf-non-embedding-via-no-regular-tree-action`.

**Other mechanisms to test.** These exclude only finitely presented hosts, not
all tree actions:
- a residually finite input whose finitely presented overgroups would have too
  hard a word problem, in the spirit of `uniform-wp-bound-excludes-bh-universal-targets`;
- inputs whose every faithful action on a rooted tree has infinitely generated
  self-similar closure (condition (N2) of the universal claim).

## Attempts

- 2026-09-13 (z3-09 lane). Braid groups do not supply an example through
  non-self-similarity alone. `B_n` for `n >= 4` is not self-similar, but it is
  residually finite and linear, so it acts faithfully on some `T_d`. If `B_n`
  embeds in `GL_m(Z)` (Zaremsky Problem 3.2), it lies in `Z^m x| GL_m(Z)`, which
  is finitely presented and self-similar by
  `principal-ideal-affine-groups-are-self-similar` with `R = Z`, `x = 2`. So a
  braid example would need a negative answer to 3.2 plus more.
