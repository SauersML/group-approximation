---
rg: 2
id: drutu-sapir-bh-via-power-map-mapping-tori
kind: route
title: The Druţu--Sapir group is a power-map ascending HNN extension of F_2, so it lies in the permutational Boone--Higman class
target: drutu-sapir-group-satisfies-boone-higman
requires:
  - power-map-free-mapping-tori-satisfy-permutational-boone-higman
  - drutu-sapir-group-index-two-squaring-mapping-torus
  - type-a-action-gives-boone-higman-for-subgroups
---

## DS is a power-map mapping torus

By (DS0) of `drutu-sapir-group-index-two-squaring-mapping-torus`,

    DS = < x, y, a | a^-1 x a = y^2, a^-1 y a = x >.

The Tietze move `t = a^-1` rewrites this as
`< x, y, t | t x t^-1 = y^2, t y t^-1 = x >`. That is `G_φ` for `n = 2`,
`x_1 = x`, `x_2 = y`, `π = (1 2)`, `m_1 = 2` and `m_2 = 1`. Indeed
`φ(x_1) = x_2^2 = y^2` and `φ(x_2) = x_1 = x`.

## Conclusion

By `power-map-free-mapping-tori-satisfy-permutational-boone-higman`, `DS` lies in
`B_A`. By `type-a-action-gives-boone-higman-for-subgroups`, it embeds in a
finitely presented simple group. ∎

## The host, unwound

- **Index two.** `k = 2` and `M_1 = M_2 = 2`. The index-two subgroup
  `K = <x, y, t^2>` is `< x, y, s | s x s^-1 = x^2, s y s^-1 = y^2 >`.
- **An affine factor is enough.** Each `Aff_i` is `BS(1,2)`, so one could use
  `B = BS(1,2) = <u, σ>` alone, with `y_1 = u` and `y_2 = z^-1 u z` in `B * <z>`.
  The proof uses the product `Aff_1 × Aff_2` only to state the general case
  uniformly.
- **Letters.** `K` embeds in `Aut_B(B * F_2) × Z`, with `F_2` free on `z_0, z`:
  - `x` and `y` act by left multiplication of `z_0` by `u^-1` and `z^-1 u^-1 z`;
  - `s` acts by the automorphism `S` fixing `B` that sends each letter
    `w ∈ {z_0, z}` to `σ^-1 w σ`, paired with the generator of `Z`. On `B * <z>`
    it restricts to `α = c_(σ^-1) ∘ β`, and `S ι(g) S^-1 = ι(β(g))`, where
    `ι(g)` sends `z_0` to `g^-1 z_0`. For `g = u` and `g = z^-1 u z` this is the
    squaring relation.
  - `S` differs from the element `T` of `pbh-relative-holomorph-closure-proof`
    by right multiplication of `z_0` by `σ`, which commutes with every `ι(g)`.
- **Actors.**
  - `Aut_B(B * F_2)` lies in `B_A` by
    `pbh-passes-to-relative-free-group-automorphisms`. Behind that claim, `B`
    sits in a finitely presented simple MIF group `M'` (BFFHZ Theorem C), and
    `Aut_M'(M' * F_2)` carries a type (A) action (BFFHZ Theorem E).
  - `K` lies in the product of that actor with an actor containing `Z`, and `DS`
    in the wreath product of this product with `S_2` (parts (a) and (b) of
    `type-a-actions-closed-under-products-and-finite-wreaths`).
- **Simple envelope.** It is the twisted Brin--Thompson group of the resulting
  actor (Zaremsky, arXiv:2405.18354, Corollary B).
