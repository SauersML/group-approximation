---
rg: 2
id: matricial-aperiodic-sft-rings-are-not-quantum-rigid-proof
kind: route
title: Push one ultraproduct coordinate to a finite field, where translations have finite order, then apply the tiling refutation of rigidity
target: matricial-aperiodic-sft-rings-are-not-quantum-rigid
requires: [periodic-quantum-tilings-refute-quantum-rigidity, sft-crossed-product-fp-iff-quantum-rigid]
artifacts:
  - research/artifacts/un-converse-subshift-models-2026-09-13-part2.md
---

1. **One coordinate.** Take the finite window `W` of `R_Ω` containing:
   - `u_i^(±1)`, the tile idempotents `χ[x_0 = a]`, and their `u^v`-conjugates for `‖v‖_∞ <= 2D+1`;
   - products of at most `|B_D|` of these, and products of pairs.

   By Łoś, one coordinate `ψ : W → M_d(F)` preserves the internal identities and keeps the tile idempotents nonzero.
2. **Finite field.** The entries of `ψ(W)` generate a finitely generated commutative domain `A`, a Jacobson ring with
   finite residue fields. A maximal ideal missing the product of one nonzero entry of each tile idempotent gives
   `π : M_d(A) → M_d(A/m)`, which keeps the internal identities and the nonvanishing.
3. **Period lattice.** `U_i = πψ(u_i)` are commuting units in a finite ring, so they have finite orders `o_i`. Set
   `E_a(z) = U^z πψ(χ[x_0 = a]) U^(−z)`, periodic under `o_1 Z × o_2 Z` and translation covariant.
4. **Axioms.**
   - (Q1) is transported from the origin.
   - (Q2) and (Q3): for `‖z' − z‖_∞ <= 2D`, the window identity `U^(z'−z) e_b U^(−(z'−z)) = πψ(u^(z'−z) χ[x_0=b] u^(−(z'−z)))`
     turns products of tile idempotents at nearby sites into images of products of commuting cylinder functions.
     These commute, and the image of an empty cylinder is 0.
   - Each `E_a(z)` is nonzero.

   So `F^d` carries a periodic quantum tiling at scale `D`, which over a finite field is a nonzero finite-dimensional
   `A_D`-module (`periodic-quantum-tilings-refute-quantum-rigidity`, item 2).
5. **Conclusion.** Item 1 of `periodic-quantum-tilings-refute-quantum-rigidity` shows that `Ω` is not `D`-quantum
   rigid, for every `D`. Then `sft-crossed-product-fp-iff-quantum-rigid` shows `R_Ω` is not finitely presented.
