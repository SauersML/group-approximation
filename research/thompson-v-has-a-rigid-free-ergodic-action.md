---
rg: 2
id: thompson-v-has-a-rigid-free-ergodic-action
kind: claim
title: Thompson's group V has a free ergodic rigid p.m.p. action, the Gaussian action of its Koopman representation on the Cantor set
distinct_from:
  rigid-actions-have-no-dbar-close-bernoulli-models: that is the d-bar lower bound for models of any rigid action and supplies rigid actions on maximally almost periodic groups; this supplies one on the simple, non-residually-finite group V.
  thompson-v-covariant-cantor-representations-are-not-amenable: that concerns covariant representations of V on the Cantor set in the operator-algebraic sense; this uses the orthogonal Koopman representation only through its Gaussian action.
---

**ESTABLISHED (unreviewed)** by [[thompson-v-has-a-rigid-free-ergodic-action-proof]].

**General principle.** Let `Γ` be a countable group and `π` a faithful orthogonal representation of `Γ` on a real
separable Hilbert space with no nonzero finite-dimensional invariant subspace. Suppose there are `g_n ∈ Γ` leaving
every finite set with `π(g_n) → 1` strongly. Then the Gaussian action `Γ ↷ (Ω, γ)` of `π` is essentially free,
ergodic, and rigid along `(g_n)`.

**Thompson's V.** Let `C = {0,1}^N` with the uniform product measure `µ`, and let `V` act by prefix replacements.
Put `κ(g) f = (d(g_*µ)/dµ)^(1/2) · f ∘ g^-1` on `L^2_R(C, µ)`. Then `κ` satisfies the principle, with `g_n` the
transposition of the cylinders `[0^n 0]` and `[0^n 1]`. So `V` has a free ergodic rigid p.m.p. action.

**Consequences.**
- By `rigid-actions-have-no-dbar-close-bernoulli-models`, shift models of this action stay at `d̄`-distance at
  least `c_λ/2` from every Bernoulli measure `λ^V`.
- By `bernoulli-measures-not-finitely-determined-at-zero-supremum`, if `h^Rok_sup(V) = 0` then no nontrivial
  finite-alphabet Bernoulli measure over `V` is finitely determined.

The simplicity of `V` enters only to rule out finite-dimensional invariant subspaces. The same argument applies
to every infinite simple group with a faithful orthogonal representation that has a rigidity sequence and no
invariant vectors.
