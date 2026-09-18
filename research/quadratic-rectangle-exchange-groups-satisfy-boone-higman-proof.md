---
rg: 2
id: quadratic-rectangle-exchange-groups-satisfy-boone-higman-proof
kind: route
title: BEx(Lambda) is the full group of the product of the Sturmian rotations
target: quadratic-rectangle-exchange-groups-satisfy-boone-higman
requires:
  - product-substitution-full-groups-satisfy-boone-higman
artifacts:
  - research/artifacts/gq-bh-bh-free-03-substitution-full-groups.md
---

1. Let `X_i` be the Cantor model of the circle with the orbit `Λ_i mod 1` doubled,
   carrying the lift of `R_{α_i}`. As in `quadratic-rotation-iet-groups-satisfy-boone-higman-proof`,
   `X_i` is a Sturmian subshift, substitutive because `α_i` is quadratic (cited, not
   read at source).
2. In `X = ∏ X_i`, every box with endpoints in the `Λ_i` is clopen, and the clopen sets
   are the finite unions of such boxes. Take `f ∈ BEx(Λ)` translating a box by
   `(s_1, ..., s_d)` with `s_i ≡ n_i α_i (mod 1)`. On that box `f` agrees with
   `R_{α_1}^{n_1} × ... × R_{α_d}^{n_d}`. So `f` lifts to a homeomorphism of `X` lying in
   `[[Z^d ↷ X]]`, and the lift is injective.
3. `product-substitution-full-groups-satisfy-boone-higman` embeds `[[Z^d ↷ X]]` in a
   finitely presented simple group.
