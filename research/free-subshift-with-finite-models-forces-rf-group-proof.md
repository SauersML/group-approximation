---
rg: 2
id: free-subshift-with-finite-models-forces-rf-group-proof
kind: route
title: Compactness gives a window on which a nontrivial element moves every point, so it acts nontrivially on a finite model
target: free-subshift-with-finite-models-forces-rf-group
requires: []
artifacts:
  - research/artifacts/sk-general-actions-a-finite-subshift-limits-2026-09-13.md
---

Direct proof, artifact §2, as follows.
- Fix `γ ≠ e`. The clopen sets `{x : x(h) ≠ x(hγ)}` cover `X` by freeness, so finitely many do, indexed by a finite `F`.
- Let `Y` be a finite subshift with `L_(F ∪ Fγ)(Y) = L_(F ∪ Fγ)(X)`. Each `y ∈ Y` agrees on `F ∪ Fγ` with some `x ∈ X`, so `y(hγ) ≠ y(h)` for some `h ∈ F`, i.e. `γy ≠ y`.
- The permutation action of `Γ` on `Y` is a homomorphism to a finite group that does not kill `γ`. ∎
