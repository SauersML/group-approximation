---
rg: 2
id: gabe-szabo-unital-uniqueness-theorem
kind: claim
title: For outer amenable actions on unital Kirchberg algebras, unital cocycle embeddings with equal KK^G-class are asymptotically unitarily equivalent
distinct_from:
  cyclotomic-class-group-counts-zp-actions-on-stable-o2: that uses Gabe--Szabó Theorem A to classify actions; this imports their unital uniqueness theorem for embeddings and the outerness criterion.
---

**ESTABLISHED (literature import).** J. Gabe and G. Szabó, *The dynamical
Kirchberg–Phillips theorem*, arXiv:2205.04933v3.

1. **Proposition 3.15.** For a countable discrete group `G` and an action
   `β : G ↷ B` on a Kirchberg algebra, `β` is isometrically shift-absorbing iff
   it is pointwise outer.
2. **Theorem 5.8.** Let `G` be exact, `A` separable unital exact with
   `α : G ↷ A`, and `B` a unital Kirchberg algebra with an amenable, isometrically
   shift-absorbing action `β`. For two unital cocycle embeddings
   `(φ, u), (ψ, v) : (A, α) → (B, β)`, `KK^G(φ, u) = KK^G(ψ, v)` iff they are
   asymptotically unitarily equivalent.
3. **Definition 1.15**, unital case with trivial cocycles. `(φ, 1)` and
   `(ψ, 1)` are asymptotically unitarily equivalent iff there is a norm-continuous
   path `u : [0, ∞) → U(B)` with:
   - `ψ(a) = lim_t u_t φ(a) u_t^*` for all `a ∈ A`;
   - `lim_t max_(g∈K) ‖1 − u_t β_g(u_t)^*‖ = 0` for every compact `K ⊆ G`.
4. **Theorem D.** Every amenable action on a separable nuclear C\*-algebra
   admits an equivariant embedding into an amenable, isometrically
   shift-absorbing action on a stable Kirchberg algebra, and that embedding
   induces a KK^G-equivalence.

Citation: `gabe-szabo-unital-uniqueness-theorem-citation`.
