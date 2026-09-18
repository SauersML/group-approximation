---
rg: 2
id: houghton-groups-embed-in-thompson-v
kind: claim
title: Every Houghton group H_n embeds in Thompson's group V, so Houghton groups satisfy Boone--Higman
distinct_from:
  houghton-groups-have-quadratic-dehn-function: that is about Dehn functions of the Houghton groups; this is an embedding in a finitely presented simple group.
  thompson-v-finitely-presented-infinite-simple: that is the classical fact that V is finitely presented and simple; this places every Houghton group inside V.
---

**ESTABLISHED** through `houghton-groups-embed-in-thompson-v-proof` (elementary; not
independently reviewed). No priority is claimed: this is standard, and the lane did not search
for a printed source.

**Statement.** Let `n >= 1`, `X = {1, ..., n} × N`, and let `H_n` be the Houghton group. It
consists of the bijections `h` of `X` that are eventually translations on each ray: there are
`K` and `m_1, ..., m_n ∈ Z` with `h(i,k) = (i, k + m_i)` for all `k >= K` and all `i`. Then
`H_n` embeds in Thompson's group `V`.

**Consequences.**
- Every Houghton group, and every subgroup of one, embeds in the finitely presented simple group
  `V` (`thompson-v-finitely-presented-infinite-simple`). So it satisfies Boone--Higman.
- `V` itself acts with a type (A) action (`pl-rearrangement-groups-have-two-transitive-orbit-actions`,
  sanity case `A = Z[1/2]`, `P = ⟨2⟩`; a lane proof, not independently reviewed). So every
  subgroup of `V`, the `H_n` included, is in the permutational class `B_A` too.
