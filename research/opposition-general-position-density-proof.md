---
rg: 2
id: opposition-general-position-density-proof
kind: route
title: Four open dense conditions on pairs of opposite points, intersected over finitely many constants, meet the dense pole pairs
target: opposition-general-position-from-nowhere-domestic-dense-poles
requires: [opposition-ping-pong-criterion-gives-mixed-identity-freeness]
---

Fix a finite `F ⊆ G ∖ {1}`. Note `O ≠ ∅`, since `Z ≠ ∅` and each `O(z)` is dense.

**Step 1: one constant.** For `g ∈ F` let `W_g` be the set of `(a, b) ∈ O` with

```text
(g·a, a) ∈ O,   (g·a, b) ∈ O,   (g·b, a) ∈ O,   (g·b, b) ∈ O.      (C1–C4)
```

Each condition is the preimage of the open set `O` under a continuous map
`Z × Z → Z × Z`, so `W_g` is open. We show that `W_g` is dense in `O`. Let
`W ⊆ O` be nonempty and open. It contains a box `U × V`, with `U` and `V`
nonempty and open.

- **(C1), (C4).** `N(g)` is closed with empty interior by (D1), so
  `U₁ = U ∖ N(g)` and `V₁ = V ∖ N(g)` are nonempty and open. Every
  `(a, b) ∈ U₁ × V₁` satisfies (C1) and (C4).
- **(C2).** Pick `a' ∈ g·U₁`, a nonempty open set. Since `O(a')` is dense,
  pick `b' ∈ V₁ ∩ O(a')`. Then `a = g⁻¹·a' ∈ U₁` and `(g·a, b') ∈ O`. So
  `{(a, b) ∈ U₁ × V₁ : (g·a, b) ∈ O}` is open and nonempty, and it contains a
  box `U₂ × V₂`.
- **(C3).** Pick `b'' ∈ V₂`. Since `O(g·b'')` is dense, pick
  `a'' ∈ U₂ ∩ O(g·b'')`, so `(g·b'', a'') ∈ O` by symmetry of `O`. So
  `{(a, b) ∈ U₂ × V₂ : (g·b, a) ∈ O}` is open and nonempty, and it contains a
  box `U₃ × V₃`.

Conditions (C1), (C2) and (C4) pass to subsets, so
`U₃ × V₃ ⊆ W ∩ W_g`, which is therefore nonempty.

**Step 2: all constants.** `W_F = ⋂_{g ∈ F} W_g` is a finite intersection of
open dense subsets of `O`, hence open and dense in `O`. For `F = ∅` put
`W_F = O`. In both cases `W_F` is nonempty and open in `O`.

**Step 3: a proximal element.** By (D2) some pole pair `(z₊, z₋)` of a proximal
`h ∈ G` lies in `W_F`. For `g ∈ F`, (C1)–(C4) at `(a, b) = (z₊, z₋)` say
`g·z_s ∈ O(z_t)` for all `s, t ∈ {+, −}`. This is (GP) for `F`.

Since `F` was arbitrary, (GP) holds. By
`opposition-ping-pong-criterion-gives-mixed-identity-freeness`, `G` is MIF. `∎`
