---
rg: 2
id: artin-ghost-ideal-is-intersection-of-two-principal-ideals
kind: claim
title: "For spherical T the ghost ideal of A_T is a free principal left ideal ZA_T·y_T, so an Artin group with two spherical maximal parabolics A_{S−u}, A_{S−v} has ghosts iff y_{S−u} and y_{S−v} have a nonzero common left multiple"
distinct_from:
  artin-ghost-ideal-localizes-to-standard-parabolics: that slices the ghost ideal along the cosets of one parabolic subgroup; this identifies the sliced pieces for spherical parabolics as free principal ideals and pins the ghost ideal down exactly as an intersection of two of them.
  artin-complex-top-homology-is-intersection-of-ideals: that identifies top homology with the intersection of the ideals ZA(1 − s); this computes that module for spherical groups (free of rank one) and uses it to replace the |S| ideals by two principal ones.
---

For an Artin group `A` on a finite set `S` let `G(A) = ⋂_{s ∈ S} ZA·(1 − s)`, the top
homology of the Artin complex (`artin-complex-top-homology-is-intersection-of-ideals`).

**Theorem.**

1. **Spherical groups.** Let `T` be a finite set with `W_T` finite. Then `G(A_T)` is a free
   left `ZA_T`-module of rank one: there is `y_T ∈ G(A_T)` with `G(A_T) = ZA_T·y_T`, and
   `a ↦ a·y_T` is injective on `ZA_T`. (For `T = {s}`, `y_T = 1 − s`.)
2. **Two spherical maximal parabolics.** Let `A` be an Artin group on `S` and `u ≠ v` in `S`
   with `T = S − {u}` and `T' = S − {v}` spherical. Then

   `G(A) = ZA·y_T ∩ ZA·y_{T'}`,

   and `(a, b) ↦ a·y_T` is an isomorphism from the module of relations
   `{(a, b) ∈ ZA² : a·y_T = b·y_{T'}}` onto `G(A)`. So `G(A) = 0` iff `y_T` and `y_{T'}` are
   left linearly independent over `ZA`: the left ideal `ZA·y_T + ZA·y_{T'}` is free on them.

**Consequence for the flagship.** Every proper subdiagram of the four compact hyperbolic
4-simplex trees `[5,3,3,3]`, `[4,3,3,5]`, `[5,3,3,5]`, `[5,3,3^{1,1}]` is spherical. By
`artin-ghost-ideals-reduce-to-four-lanner-trees`, the top-degree part of the K(π,1)
conjecture for all Artin groups is therefore equivalent to: **for each of these four diagrams
and one (equivalently, every) pair `u ≠ v`, the elements `y_{S−u} ∈ ZA_{S−u}` and
`y_{S−v} ∈ ZA_{S−v}` have no nonzero common left multiple in `ZA`.** Both directions hold.

**Calibration.**

- If `W_S` is finite, `x_S = Σ_{w ∈ W_S} (−1)^{ℓ(w)} σ(w)` is a nonzero common left multiple.
- If `m_uv = ∞`, the group is the amalgam `A_T *_{A_{T ∩ T'}} A_{T'}`, which has an edge
  labelled `∞`, so `G = 0` by `artin-ghost-ideal-localizes-to-standard-parabolics`: the two
  generators are independent.
- For the four trees take `u, v` non-adjacent (`m_uv = 2`). Then `A` is the quotient of the
  amalgam `B = A_T *_{A_{T ∩ T'}} A_{T'}` by the single relation `uv = vu`. The question is
  whether this one commutation relation creates a common left multiple of `y_T` and
  `y_{T'}`, which are independent in `ZB`.

`y_T` is the class of the boundary of the top cell of the Salvetti complex, transported
through the nerve theorem. `x_T` lies in `G(A_T)`, so `x_T = c·y_T` for some `c ∈ ZA_T`, and
mapping to `ZW_T` shows `Σ_g c_g (−1)^{ℓ(g)} = ±1`. Whether `c = ±1` is not decided here, and
the theorem does not need it.

Proof route: `artin-ghost-ideal-is-intersection-of-two-principal-ideals-proof`.
