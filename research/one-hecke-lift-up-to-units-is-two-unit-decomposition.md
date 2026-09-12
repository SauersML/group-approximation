---
rg: 2
id: one-hecke-lift-up-to-units-is-two-unit-decomposition
kind: claim
title: A one-letter Hecke lift up to corner units is exactly a two-unit decomposition of s0
distinct_from:
  bare-one-hecke-letter-cannot-lift-s0: that fixes both edge units to the identity and refutes the resulting choice; this characterizes the remaining scaled variant without asserting it exists.
  leavitt-rank-three-unit-lift: that constructs a sum of three units; this identifies the strictly sharper two-unit input needed by the proposed Hecke construction.
  binary-leavitt-family-lifts-into-unit-corner: that asks to lift four generators with all five relations; this asks only for the additive shape of one generator's corner lift.
artifacts:
  - research/artifacts/one-nonnormal-packet-corner-correction-2026-08-21.md
---

There are units `p,q,y in R^x` with

```text
p(1+y)q=s_0
```

if and only if `s_0` is a sum of two units.  The forward decomposition is
`s_0=pq+pyq`; conversely `s_0=a+b` gives
`s_0=a(1+a^-1b)`.  Hence corner-unit scaling does not evade the failed bare
literal automatically; it replaces it by the presently unproved two-unit
decomposition problem.

