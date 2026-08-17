---
rg: 2
id: simple-core-bi-index-counts-coset-action-pair-orbits-proof
kind: route
title: The kernel is the normal core, and every pair moves to one based at the trivial coset
target: simple-core-bi-index-counts-coset-action-pair-orbits
requires: []
artifacts:
  - research/artifacts/boone-higman-audit-2026-08-17.md
---

**Faithfulness.**  The kernel of `Gamma` acting on `Gamma/S` is the normal
core

    C = Core_Gamma(S) = intersection over gamma of  gamma S gamma^{-1} .

`C` is normal in `Gamma` and `C <= S`.  Since `S != Gamma` we have
`C != Gamma`, so `C` is a proper normal subgroup, and
`proper-normal-subgroups-miss-the-normally-generating-core` gives

    C = C ∩ S = 1 .

**Pair-orbits are double cosets.**  The action on `Gamma/S` is transitive, so
every ordered pair of cosets can be carried to one of the form `(S, gS)`.
Two such, `(S, gS)` and `(S, hS)`, lie in the same `Gamma`-orbit iff some
element carrying `S` to `S` — that is, some element of the point stabilizer
`S` — carries `gS` to `hS`; iff `h in S g S`.  So the map
`SgS |-> orbit of (S, gS)` is a well-defined bijection from `S \ Gamma / S`
onto the set of pair-orbits.

**Point stabilizer.**  The stabilizer of the coset `S` is `S` itself, and the
action is transitive, so every point stabilizer is conjugate to `S`.

∎

## The one place the hypotheses are consumed

Simplicity of `S` and the normal generator are used exactly once, in
`C = 1`.  Everything else is generic coset combinatorics valid for any
subgroup of any group.  So the faithfulness clause is the whole reason this
route needs the near-solution at all; without it the coset action could have
an enormous kernel and `SV_Gamma` would be relatively simple rather than
simple.
