---
rg: 2
id: measure-rf-class-iff-measured-subshifts-window-periodic-proof
kind: route
title: Theorem N via name maps (⇐) and a Cantor factor with trivial action (⇒)
target: measure-rf-class-iff-measured-subshifts-window-periodic
requires: [rf-subshifts-are-periodic-window-approximable]
artifacts:
  - research/artifacts/un-class-n-conjecture-2026-09-13-part1.md
---

Full proof: artifact part 1, §1 (Theorem N).

- **(⇐).** For a Cantor system `α : Γ ↷ Z` with full-support `μ`, fix a clopen partition `𝒬` of mesh `< ε` and
  the equivariant name map `π(z)(γ) = i ⇔ α(γ^(-1))z ∈ Q_i`. `X = π(Z)` carries `π_*μ` of full support. Take
  `W = {e} ∪ F^(-1)` and the finite invariant `O ⊆ X_W`; choose `ζ(c)` with `π(ζ(c))|_W = c|_W`. Then
  `π(α(s)ζ(c))(e) = c(s^(-1)) = π(ζ(s·c))(e)` for `s ∈ F`, so both points lie in one atom, and `ζ(O)` meets every
  atom. Lemma 1 (maps suffice), proved in the artifact of `rf-subshifts-are-periodic-window-approximable`, gives RF.
- **(⇒).** For `X` with full-support `μ`, `Z = X × {0,1}^N` (trivial action on the second factor, Bernoulli
  measure) is a Cantor system with a full-support invariant measure, hence RF. For a model `(E, β)` close on
  `W^(-1)` at a scale `2^(-j)` with `W ⊆ B_j`, put `y_z(λ) = x_(β(λ^(-1))z)(e)`. Then `y_(β(g)z) = g·y_z`,
  `y_z|_W = x_z|_W ∈ L_W(X)`, every translate has legal `W`-windows, and density covers `L_W(X)`. This is the
  (⇒) argument of Proposition S, which never used perfectness of `X`.
