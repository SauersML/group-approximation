---
rg: 2
id: clopen-towers-at-every-scale-iff-topologically-free-proof
kind: route
title: Proof of the tower equivalence, by separating a point of the complement of the fixed sets
target: clopen-towers-at-every-scale-iff-topologically-free
requires: []
artifacts:
  - research/artifacts/sk-strong-4-boundaries-2026-09-13-part1.md
---

Direct proof; artifact §2.

**(1) ⇒ (2).** `Y = ⋃_{γ ∈ F\{e}} Fix(γ)` is a finite union of closed sets with empty interior, so
`Y` is closed with empty interior and `U \ Y` is nonempty open. Pick `x ∈ U \ Y` and a clopen
`U' ⊆ U` with `x ∈ U'`. For each `γ ∈ F \ {e}` we have `γx ≠ x`, so zero-dimensionality gives
disjoint clopen sets `A_γ ∋ x` and `B_γ ∋ γx`. Put
`V = U' ∩ ⋂_{γ ∈ F\{e}} (A_γ ∩ γ^{-1}B_γ)`. Each `γ^{-1}B_γ` is clopen, so `V` is clopen, and
`x ∈ V` because `x ∈ A_γ` and `γx ∈ B_γ`. For `γ ∈ F \ {e}`, `V ⊆ A_γ` and `γV ⊆ B_γ`, which are
disjoint, so `γV ∩ V = ∅`.

**(2) ⇒ (1).** If `γ_0 ≠ e` and `Fix(γ_0)` contains a nonempty open `U_0`, apply (2) with
`F = {γ_0}` and `U = U_0`. The resulting nonempty clopen `V` lies in `Fix(γ_0)`, so `γ_0V = V` and
`γ_0V ∩ V = V ≠ ∅`, contradicting `F`-freeness.

**The consequences.** Given a nonempty open `W`, it meets some atom `P ∈ 𝒫`, and `W ∩ P` is
nonempty open, so (2) gives an admissible `V ⊆ W ∩ P`. If `h` is locally constant and `h ≠ 0`,
then `γ^{-1}{h ≠ 0}` is nonempty open, so it contains an admissible `V`, and then `γV ⊆ {h ≠ 0}`,
so `h` does not vanish on `γV`. Taking `γ = e` gives the first form.
