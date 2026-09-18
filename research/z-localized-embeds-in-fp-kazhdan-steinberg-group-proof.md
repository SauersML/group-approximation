---
rg: 2
id: z-localized-embeds-in-fp-kazhdan-steinberg-group-proof
kind: route
title: The resolvent corner exists already in R_l, and x_12 carries it into the finitely presented Steinberg group
target: z-localized-embeds-in-fp-kazhdan-steinberg-group
requires:
  - rf-resolvent-ring-has-z-localized-corner
  - resolvent-ring-presentation-is-not-faithful-on-r-bar
  - steinberg-finite-presentation-and-kazhdan-theorem
---

**1. θ in R_l.** Every step of item 4 of `rf-resolvent-ring-has-z-localized-corner-proof`
uses only the eight defining relations.
- From `x u = (u+l) x` and `x x' = 1` we get `x u x' = u + l`, hence
  `x^k u x^(-k) = u + kl`. So `u + m`, for `m = 1 + kl`, is a unit with inverse
  `x^k B x^(-k)`.
- `u` commutes with `u + m`, hence with its inverse. `e` commutes with `u`, since
  `u e = 0 = e u`, hence with `u + m` and its inverse.
- So `y_m = (u+m)^(-1) e` lies in `e R_l e`, the ring `C = Z[e, y_m]` is commutative
  with unit `e`, and `m y_m = e`, since `(u+m) e = m e`.
- Every integer prime to `l` is then invertible in `C` (Fermat), so `n -> n e`
  extends to `θ : Z_(l) -> C`.

The map `R_l -> R̄_l` sends the generators to the generators, so it carries this
`θ` to the `θ` of the model, which is injective.

**2. Injectivity in St_N.** `x_12(a) x_12(b) = x_12(a+b)` is a Steinberg relation, so
`c -> x_12(θ(c))` is a homomorphism. Compose with
`St_N(R_l) -> E_N(R_l) -> E_N(R̄_l) ⊆ GL_N(R̄_l)`. It sends `x_12(θ(c))` to the
elementary matrix `e_12(θ(c))`, which is the identity only if `θ(c) = 0` in `R̄_l`,
i.e. `c = 0`.

**3. Imports.** `R_l` is a unital associative ring with 5 generators and 8
relations, so it is finitely presented. Apply
`steinberg-finite-presentation-and-kazhdan-theorem` with `n = N >= 4`. ∎
