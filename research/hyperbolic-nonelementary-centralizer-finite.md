---
rg: 2
id: hyperbolic-nonelementary-centralizer-finite
kind: claim
title: Centralizers of non-elementary subgroups of hyperbolic groups are finite
distinct_from:
  non-residually-finite-hyperbolic-group: that is the open counterexample target; this is an established structural fact about centralizers in hyperbolic groups, mentions no finite quotient and no residual finiteness, and is consumed only as an input to two obstruction claims
artifacts:
  - research/artifacts/hyperbolic-residual-finiteness-audit-2026-08-17.md
---

Let `G` be word-hyperbolic and let `Γ ≤ G` be non-elementary.  Then

```text
|C_G(Γ)| < infinity.
```

Standard hyperbolic group theory; recorded here because two obstruction
claims in this graph consume it and nothing else in the corpus states it.

Two riders used downstream:

- An **infinite** subgroup with property (T) inside a hyperbolic group is
  automatically non-elementary: an infinite elementary subgroup is virtually
  cyclic, hence infinite amenable, and an infinite amenable group does not
  have (T) (`bekka-valette-amenable-t-dichotomy`).  So every hypothesis of
  the form "infinite Kazhdan subgroup of a hyperbolic group" already supplies
  non-elementarity.
- The conclusion is finiteness, not triviality.  `G` may well have a nontrivial
  finite centre, and `C_G(Γ)` contains it; what fails is any *infinite*
  centralizing subgroup, which is what the compression architectures need.
