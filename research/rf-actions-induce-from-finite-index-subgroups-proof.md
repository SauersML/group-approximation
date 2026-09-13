---
rg: 2
id: rf-actions-induce-from-finite-index-subgroups-proof
kind: route
title: The induced finite action over a transversal follows the ambient action up to translates of the subgroup model's error
target: rf-actions-induce-from-finite-index-subgroups
requires: []
artifacts:
  - research/artifacts/un-rf-beyond-free-2026-09-13-part1.md
---

Artifact part 1, §3, Proposition I.
- Fix a transversal `T ∋ e`, `Γ = ⊔_(t∈T) tH`. For `γ ∈ F`, `t ∈ T` write `γt = t'h`; collect these `h` in `F_H`.
- Choose `δ` with `d(x,x') < δ ⇒ d(tx,tx') < ε/2` for `t ∈ T`, and an RF model `(E_H, β_H)` of `α|_H` for `(F_H, δ)`
  that is also `ε`-dense.
- `Γ` acts on `T × E_H` by `γ(t,z) = (t', β_H(h)z)`, the induced action `Γ ×_H E_H`. Put `ζ(t,z) = α(t)z`.
- `ζ(γ(t,z)) = α(t')β_H(h)z` and `α(γ)ζ(t,z) = α(t')α(h)z` are `ε/2`-close, and `ζ(e,z) = z` gives density.
- Lemma 1 of the artifact (perfectness) makes `ζ` injective.
