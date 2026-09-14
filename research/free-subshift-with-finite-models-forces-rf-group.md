---
rg: 2
id: free-subshift-with-finite-models-forces-rf-group
kind: claim
title: A group acting freely on a subshift that is a limit of finite subshifts is residually finite
distinct_from:
  rf-subshifts-are-periodic-window-approximable: that characterizes Kerr–Nowak residual finiteness of a perfect subshift by covering finite orbits; this shows that, for a free action, such finite orbits exist only over residually finite acting groups.
artifacts:
  - research/artifacts/sk-general-actions-a-finite-subshift-limits-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `Γ` be a group, `A` finite, and `X ⊆ A^Γ` a nonempty subshift on which `Γ` acts freely, with `(γx)(h) = x(hγ)`. Suppose that for every finite `F ⊆ Γ` some finite invariant `Y ⊆ A^Γ` has `{y|_F : y ∈ Y} = {x|_F : x ∈ X}`. Then `Γ` is residually finite.

**Proof.**
- Let `γ ≠ e`. Freeness means the clopen sets `{x : x(h) ≠ x(hγ)}`, `h ∈ Γ`, cover `X`. By compactness some finite `F ∋ e` has: every `x ∈ X` satisfies `x(h) ≠ x(hγ)` for some `h ∈ F`.
- A finite subshift `Y` with the `(F ∪ Fγ)`-patterns of `X` then has `(γy)(h) = y(hγ) ≠ y(h)` for each `y ∈ Y` and some `h ∈ F`.
- So `γ` survives in the finite quotient `Γ → Sym(Y)`. ∎

**Model test.** Freeness is needed: constant configurations form a finite subshift over any group.

**Consequence.** `finite-model-subshift-elementary-groups-simple-kazhdan-lef` reaches exactly the residually finite acting groups (with `rf-groups-have-free-minimal-subshifts-with-finite-models`).

Route: `free-subshift-with-finite-models-forces-rf-group-proof`.
