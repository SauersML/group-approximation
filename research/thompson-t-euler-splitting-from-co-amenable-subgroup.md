---
rg: 2
id: thompson-t-euler-splitting-from-co-amenable-subgroup
kind: route
title: "Induce the homomorphism u of the preimage of a co-amenable H to a cocycle over T/H; the quasi-regular representation has almost invariant vectors"
target: thompson-t-euler-class-splits-over-almost-invariant-space
requires:
  - thompson-t-co-amenable-subgroup-kills-real-euler-class
---

Let `H` and `u : H̄ → R` with `u(z) = 1` be as in
`thompson-t-co-amenable-subgroup-kills-real-euler-class`.

Take `X = T/H = T̄/H̄` with counting measure. The action is by permutations, so it is measure
preserving, and its Koopman representation is the quasi-regular representation `ℓ²(T/H)`. By
co-amenability (Eymard's equivalence; standard), `ℓ²(T/H)` has almost invariant vectors.

Choose a section `σ : T̄/H̄ → T̄` and put `β(g, y) = u(σ(gy)^{-1} g σ(y))`. The argument lies in
`H̄`, because `g σ(y) H̄ = gy = σ(gy) H̄`.
- *Cocycle identity.*
  `σ(ghy)^{-1} gh σ(y) = [σ(ghy)^{-1} g σ(hy)] · [σ(hy)^{-1} h σ(y)]`, and `u` is a
  homomorphism, so `β(gh, y) = β(g, hy) + β(h, y)`.
- *Normalization.* `zy = y` and `z` is central, so `β(z, y) = u(σ(y)^{-1} z σ(y)) = u(z) = 1`.

So `(X, β)` witnesses the target. ∎
