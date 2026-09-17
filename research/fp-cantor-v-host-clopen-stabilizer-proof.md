---
rg: 2
id: fp-cantor-v-host-clopen-stabilizer-proof
kind: route
title: Inherit faithfulness, transitivity and the five pair orbits from V, leaving only the stabilizer
target: fp-cantor-groups-containing-v-type-a-iff-clopen-stabilizer-fg
requires:
  - fp-full-binary-cantor-groups-have-type-a-actions
  - type-a-action-gives-boone-higman-for-subgroups
---

Notation as in the target.

**Step 1. Faithful.** Let `1 ≠ f ∈ Γ`. Pick `κ` with `fκ ≠ κ` and a cone `U ∋ κ` so
small that `fU ∩ U = ∅` (continuity, Hausdorff). Then `fU ≠ U`, and `U ∈ Ω`.

**Step 2. Orbits.** `V` is finitely presented, full, and contains standard `V`. So by
`fp-full-binary-cantor-groups-have-type-a-actions`, `V ↷ Ω` has seven orbits on ordered
pairs and five on two-element subsets.
- Transitivity: two proper nonempty clopens are unions of `m ≥ 1` and `m' ≥ 1` cones whose
  complements are unions of `n, n' ≥ 1` cones. After subdividing cones so that
  `m = m'` and `n = n'`, the prefix replacement matching cones is an element of `V`. So
  `V` is transitive on `Ω`.
- `Γ ⊇ V` has coarser orbits: it is transitive, with at most five orbits on two-element
  subsets.

**Step 3. Item 2.**
- Type (A) needs faithfulness (Step 1), finite presentation (given), finitely many orbits
  of two-element subsets (Step 2) and finitely generated point stabilizers.
- Point stabilizers are pairwise conjugate by transitivity, so one is finitely generated
  iff all are.

**Step 4. Item 3.** Zaremsky Corollary B, quoted in
`type-a-action-gives-boone-higman-for-subgroups`.
