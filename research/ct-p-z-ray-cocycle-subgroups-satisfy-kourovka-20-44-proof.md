---
rg: 2
id: ct-p-z-ray-cocycle-subgroups-satisfy-kourovka-20-44-proof
kind: route
title: "Frozen tails along the chain K_s = s v + D·1: tracked tails stay on the chain, are read only near the corner D·1, and otherwise give an orbit invariant of positive density"
target: ct-p-z-ray-cocycle-subgroups-satisfy-kourovka-20-44
requires:
  - ct-p-z-is-a-one-vertex-k-graph-full-group
---

Lane proof (bh-free-58, 2026-09-19), not reviewed. The full argument is in the body of
`ct-p-z-ray-cocycle-subgroups-satisfy-kourovka-20-44`.

The only input is the k-graph description of `CT_P(Z)` for finite `P`:
- classes with `P'`-smooth moduli are cylinders;
- class-wise canonical maps are prefix replacements;
- the tails `σ^n` compose.

This is item 3 and the k-graph section of `ct-p-z-is-a-one-vertex-k-graph-full-group`.
Everything else (tracking, reversal by inverse tables, the chain, the counting) is proved in
the claim's body.
