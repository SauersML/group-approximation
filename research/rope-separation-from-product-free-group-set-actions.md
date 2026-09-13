---
rg: 2
id: rope-separation-from-product-free-group-set-actions
kind: route
title: Sofic set actions of products of free groups make the compiler's first rope sofic, which gives the separating rope models
target: centralizing-hnn-perturbed-edge-separation
requires:
  - product-of-free-groups-set-actions-are-sofic
  - compiler-rope-edge-is-not-co-amenable
---

Conditional route. It fires once
[[product-of-free-groups-set-actions-are-sofic]] is established.

1. The two-sided action `F(X_e) x F(X_e) ↷ H_e`, `(g,h).q = g q h^-1`, is an
   action of a product of two free groups on a countable set. So it is sofic
   by the premise.
2. By (R3) of [[compiler-rope-edge-is-not-co-amenable]],
   `Gamma_e = < K_e, v | [v, L_e] = 1 >` is sofic.
3. Take a sofic approximation `sigma` of `Gamma_e` that is multiplicative and
   nearly free on a ball containing the tested edge generators, the finite
   ball of `K_e`, and the finite packet `W`. Put `pi = sigma|_(K_e)` and
   `sigma_v = sigma(v)`. For `l in L_e`, `[v,l] = 1` in `Gamma_e`, so
   multiplicativity makes `[sigma_v, pi(l)]` close to the identity in
   normalized Hamming distance. That is item 1 of the target. Each nontrivial
   Britton-reduced `w in W` is a nontrivial element of `Gamma_e`, so
   `sigma(w)` moves almost every point. Multiplicativity lets us replace
   `sigma(w)` by the product of `sigma` of its letters. That is item 2, with
   fraction tending to `1`.
4. `pi` does not factor through a finite quotient of `K_e`. By
   [[centralizing-hnn-sofic-via-regular-edge-centralizer]] such a model would
   kill every pinch at a closure point of `L_e`. This agrees with the
   no-go and adds no hypothesis.

Scope: this is only the first rope. The positive branch of
`sofic-safe-finite-presentation-compiler` also needs the twisted rope over
`S_e`, which is not a free generalized wreath product.
