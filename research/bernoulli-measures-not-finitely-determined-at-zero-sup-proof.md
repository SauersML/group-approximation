---
rg: 2
id: bernoulli-measures-not-finitely-determined-at-zero-sup-proof
kind: route
title: Models of a rigid action approach the Bernoulli measure weak* at zero supremum, carry the same zero Rokhlin entropy, and stay d-bar far
target: bernoulli-measures-not-finitely-determined-at-zero-supremum
requires:
  - rigid-actions-have-no-dbar-close-bernoulli-models
  - rokhlin-entropy-is-the-bernoulli-approximation-threshold
  - seward-per-group-rokhlin-entropy-of-bernoulli-shifts
  - positive-rokhlin-entropy-action-gives-positive-supremum
  - seward-bernoulli-measures-finitely-determined-under-rbs
---

Notation as in the target. Let `G ↷ (X, µ)` be a rigid free ergodic p.m.p. action.

**Theorem.**
- **Rokhlin entropy of X.** If `h^Rok_G(X) = ∞`, then `X` has positive Rokhlin entropy, and the fourth
  prerequisite gives `h^Rok_sup(G) > 0`, a contradiction. So `h^Rok_G(X)` is finite, hence at most the
  supremum, and `h^Rok_G(X) = 0`.
- **Weak* approximation.** `λ` is not a point mass, so `H(λ) > 0 = h^Rok_G(X)`. Item 1 of the second
  prerequisite puts `λ^G` in the weak* closure of the set of shift models `ν ∈ M_G(L^G)` isomorphic to `X`. So
  every weak*-neighbourhood `U` of `λ^G` contains such a `ν`.
- **The conditions of the definition hold.** `(L^G, ν) ≅ X`, so `ν` is ergodic and essentially free, and
  `h_G(L^G, ν) = h^Rok_G(X) = 0` because Rokhlin entropy is an isomorphism invariant. The Bernoulli shift
  `(L^G, λ^G)` with non-degenerate base is essentially free, so `Stab_*(ν) = Stab_*(λ^G)` is the point mass at
  the trivial subgroup. Theorem 1.10 of the third prerequisite gives
  `h_G(L^G, λ^G) = min(H(λ), h^Rok_sup(G)) = 0`. So `|h_G(L^G, ν) − h_G(L^G, λ^G)| = 0 < δ` for every `δ > 0`.
- **d-bar.** The first prerequisite gives `d̄(ν, λ^G) ≥ c_λ/2`.

With `ε = c_λ/4` in the definition of the fifth prerequisite, no pair `(U, δ)` works. So `λ^G` is not finitely
determined.

**Corollary.** Let `G` be infinite and maximally almost periodic. The first prerequisite supplies a rigid free
ergodic action. If `h^Rok_sup(G) = 0`, the theorem shows that no nontrivial `λ^G` is finitely determined. So a
finitely determined nontrivial `λ^G` forces `h^Rok_sup(G) > 0`. Then some free ergodic action has Rokhlin
entropy in `(0, ∞]`, by the definition of the supremum.

**RBS remark.** Suppose `h_G(L^G, λ^G) = H(λ)`, and let `X` be rigid, free and ergodic with
`h^Rok_G(X) = H(λ)`. Fix `ε = c_λ/4`, and let `(U, δ)` be given by the fifth prerequisite. Any model `ν` of `X`
in `U` satisfies the entropy and stabilizer conditions, so `d̄(ν, λ^G) < c_λ/4`. That contradicts the first
prerequisite, so `U` contains no model of `X`.
