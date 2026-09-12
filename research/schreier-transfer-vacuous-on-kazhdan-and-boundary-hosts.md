---
rg: 2
id: schreier-transfer-vacuous-on-kazhdan-and-boundary-hosts
kind: claim
title: The fixed-configuration transfer gives only constants on simple Kazhdan hosts and nothing at point stabilizers of measure-free actions
distinct_from:
  simple-kazhdan-groups-have-no-proper-co-amenable-subgroups: that is the group-theoretic fact about co-amenable subgroups, recorded for Rokhlin lower bounds; this applies it to the fixed-configuration transfer, where it removes every subgroup but the host.
  separating-repetitive-amenable-schreier-families-force-soficity: that bounds what the transfer can decide on any group; this shows the transfer yields not even a filter on infinite simple Kazhdan hosts, or at point stabilizers of Thompson's V.
artifacts:
  - research/artifacts/subgroup-fixed-configuration-transfer-2026-09-12.md
---

**ESTABLISHED** by `schreier-transfer-vacuity-proof`.

Let `D` be a finite label set generating `G`, as it does for a strict design on its table group
(`table-groups-are-memory-holonomy-groups`).

1. **Simple Kazhdan hosts.** If `G` is infinite, simple and Kazhdan, the only subgroup with an
   amenable Schreier graph `H\G` is `G` itself. So Theorem B of the artifact places only the constant
   configurations in the image, and they lie in every injective image anyway. The Garden of Eden filter
   says only that Garden of Eden patterns are nonconstant.
2. **Point stabilizers of measure-free actions.** If `G` acts continuously on a compact Hausdorff
   space `Y` with no invariant Borel probability measure, then no point stabilizer `G_y` has an amenable
   Schreier graph. This covers Thompson's `V` acting on the Cantor set: the prefix maps
   `0 -> 00, 10 -> 01, 11 -> 1`, `00 <-> 01`, and `0 <-> 1` force `mu[0] = 2 mu[0]` and `mu[1] = mu[0]`.

**Consequence.** On the reduced hosts of `gottschalk-reduces-to-fg-simple-kazhdan-groups`, the transfer
is empty. On `V` its natural subgroups fail too. Any positive use of fixed configurations there needs
Schreier graphs that are nonamenable, where Theorem B's counting does not apply.

Proof: Section 4 of the artifact.
