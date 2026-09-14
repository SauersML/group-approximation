---
rg: 2
id: clopen-towers-at-every-scale-iff-topologically-free
kind: claim
title: A group action on a zero-dimensional compact space admits clopen towers inside every open set iff the action is topologically free
artifacts:
  - research/artifacts/sk-strong-4-boundaries-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed).** Let a countable group `Γ` act by homeomorphisms on a compact
Hausdorff zero-dimensional space `X`. Call a clopen `V ⊆ X` *`F`-free*, for a finite `F ⊆ Γ`, if
`γV ∩ V = ∅` for every `γ ∈ F \ {e}`. The following are equivalent.

1. The action is topologically free: `Fix(γ) = {x : γx = x}` has empty interior for every `γ ≠ e`.
2. For every finite `F ⊆ Γ` and every nonempty open `U ⊆ X` there is a nonempty `F`-free clopen
   `V ⊆ U`.

Quantifying over all nonempty open `U` is what makes this an equivalence: the weaker statement
with `U = X` holds for many actions that are not topologically free, because `V` can be chosen
away from the fixed region.

Two consequences used downstream, for a topologically free action, a finite `F ⊆ Γ` and a finite
clopen partition `𝒫` (call `V` *admissible* if it is nonempty clopen, `F`-free and inside one atom
of `𝒫`):
- every nonempty open set contains an admissible `V`;
- a locally constant `h : X → k` vanishing on `γV` for every admissible `V`, for one fixed
  `γ ∈ Γ`, is `0`.

The admissible sets do not cover `X` when some point has a nontrivial stabilizer, and no partition
of `X` into `F`-free sets need exist; they cover the dense open set
`X \ ⋃_{γ ∈ F\{e}} Fix(γ)`, and a locally constant function is determined there.

Route: `clopen-towers-at-every-scale-iff-topologically-free-proof`.
