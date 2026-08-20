---
rg: 2
id: balanced-product-frame-index-expansion
kind: claim
title: Balanced-product coboundary expansion forces marked frame-index twist to positive density
distinct_from:
  extensive-cosystolic-index-defect: that is the full presentation-level endpoint for arbitrary local indices; this specializes the expansion step to the quantum context-frame index and group-algebra orbit checks.
  quantum-context-frame-index: that constructs and locally charges one index; this turns the marked global twist into extensively many nonzero local indices with bounded overlap.
---

Choose a bounded-degree balanced-product chain complex whose cells are finitely
many group orbits.  Label its overlap edges by the indices of
`quantum-context-frame-index`.  If the marked word twists the total index, then
small-set coboundary expansion forces

```text
#{edges with nonzero index} >= gamma * rank(marked carrier),  (BPF1)
```

with `gamma>0` independent of the cover size.  Each local relator occurs in at
most `D` index neighborhoods.  Genuine coherent quantum solutions label every
edge by zero, so `(BPF1)` does not confuse quantum contextuality with classical
unsatisfiability.

## Attempts

- Use a bounded-degree balanced-product complex with one orbit per frame
  overlap and apply small-set coboundary expansion to the `Z_2` labels.
- The deferred interface is geometric: the marked word must equal the global
  cohomology twist of the local frame indices. Expansion cannot create that
  twist or repair an HS-unstable index.
