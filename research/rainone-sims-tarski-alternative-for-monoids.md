---
rg: 2
id: rainone-sims-tarski-alternative-for-monoids
kind: claim
title: Tarski's alternative for monoids - an element is completely non-paradoxical iff some state normalizes it
---

Let `(S, +)` be an abelian monoid with the algebraic ordering and `θ ∈ S`. The following are
equivalent:

1. `(n+1) θ ≰ n θ` for every `n ∈ N`.
2. There is a non-trivial state `ν : S -> [0, ∞]` with `ν(θ) = 1`. Here a state is additive,
   order-preserving, and satisfies `ν(0) = 0`.

Consequence used in `un-paradox`: if no state normalizes `θ`, then `(k+1)θ <= kθ` for some `k`, and
adding `θ` repeatedly gives `2kθ <= kθ`.
