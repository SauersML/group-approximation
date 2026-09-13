---
rg: 2
id: sft-crossed-product-fp-iff-quantum-rigid-proof
kind: route
title: Local presentations, a sitewise representation, and the universal property of the crossed product
target: sft-crossed-product-fp-iff-quantum-rigid
requires: []
artifacts:
  - research/artifacts/sft-crossed-product-presentation-rigidity-2026-09-13.md
---

The artifact, Sections 1 and 2, gives the complete proof. Outline:

1. **Local presentations.** `A_D` has generators `e_a`, `u_1^(±1)`, `u_2^(±1)`, with
   `P_h^a = u^h e_a u^(-h)`. Its relations: the `u_i` commute and are invertible; the `e_a` form a
   partition; `e_a` commutes with `P_h^b` for `|h| <= 2D`; and forbidden `D`-ball patterns
   vanish.
   - A word of length `<= D` normal-orders to (commuting `P`'s on `B_D`) times `u^g`.
   - Occurring pattern idempotents times group elements are independent in `R_Ω`.
   - So every relation of `R_Ω` of length `<= D` already holds in `A_D`. Hence `R_Ω` is finitely
     presented iff `A_D -> R_Ω` is an isomorphism for some `D`.
2. **Only if.** Given a family `E` on `W`, let `A_D` act on finitely supported `W`-valued functions
   on `Z^2` by `e_a -> E_a(w)` at site `w` and `u^g` by translation. Then `P_h^a` acts by
   `E_a(w + h)`, and (Q1)–(Q3) are the relations of `A_D`. If `A_D = R_Ω`, the global commutation
   relations of `R_Ω` give `[E_a(w), E_b(w + h)] = 0` for all `h`.
3. **If.** Left multiplication by `P_z^a` on `W = A_D` is such a family, so rigidity makes the
   `P_z^a` commute in `A_D`.
   - By Stone duality, the commutative algebra they generate is a quotient of `LC(Y_D, k)`, where
     `Y_D` is the space of configurations whose `D`-ball patterns all occur in `Ω`. Since `D >= r`,
     `Y_D = Ω`.
   - The universal property of the algebraic crossed product then inverts `A_D -> R_Ω`.
