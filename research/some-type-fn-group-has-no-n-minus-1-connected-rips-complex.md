---
rg: 2
id: some-type-fn-group-has-no-n-minus-1-connected-rips-complex
kind: claim
title: Some group of type F_n with n >= 3 has no (n-1)-connected Rips complex
---

There are `n >= 3` and a group `G` of type `F_n` such that for every finite
generating set `S` of `G` and every `t >= 0` the Rips complex `R_t(G,S)` is
not (n−1)-connected.

This is the negative answer to Zaremsky Problem 4.4. By
`fp-groups-have-simply-connected-rips-complexes` no such group exists for
`n <= 2`.

## Attempts

- Obstructions cannot come from homological finiteness of `G` alone. A group
  of type `F_n` has free cocompact (n−1)-connected complexes, and the chain
  complex of an (n−1)-connected Rips complex is just another finite-type
  partial resolution. Any proof of this claim must use what is special about
  Rips complexes: one free vertex orbit and the flag condition, i.e. the
  combinatorics of cliques in Cayley graphs
  (`group-rips-complexes-are-cayley-graph-flag-complexes`).
- Ruled out, 2026-09-13: Bestvina–Brady groups, including the Bieri–Stallings
  groups of type `F_n` not `F_{n+1}`
  (`bestvina-brady-groups-have-connected-rips-complexes`); direct products of
  groups with (n−1)-connected Rips complexes
  (`connected-rips-complexes-pass-to-direct-products`); hyperbolic groups and
  `Z^n` (contractible at large scale).
- Candidate families to test: groups of type `F_n` whose Rips complexes are
  hard to analyze at every scale and that no cube-level-set method reaches:
  higher-rank lattices such as `SL_3(Z)` (type `F_∞`, Kazhdan, not
  cubulable), Thompson-type groups at a fixed `n`, `F_n`-not-`F_{n+1}` groups
  that are not Bestvina–Brady kernels. Nothing found as of 2026-09-13.
