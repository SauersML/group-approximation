---
rg: 2
id: tensor-product-algebra-fp-iff-factors-fp
kind: claim
title: A tensor product of two nonzero finitely generated algebras over a field is finitely presented exactly when both factors are, so boundary and Leavitt stabilization cannot create finite presentation
distinct_from:
  sft-crossed-product-fp-iff-quantum-rigid: that characterizes finite presentation of one SFT crossed product; this transfers finite presentation through tensor products, so a product host LC(Ω × Y) ⋊ (P × Q) is finitely presented only if LC(Ω) ⋊ P is.
  fp-crossed-products-force-sft-over-any-group: that forces finite type from finite presentation over one acting group; this shows product hosts inherit every such obstruction from each factor.
---

**ESTABLISHED (unreviewed).** Let `k` be a field and `A, C` nonzero finitely generated unital `k`-algebras.
Then `A ⊗_k C` is finitely presented iff `A` and `C` are.

**Consequences for the crossed-host route.**
1. **Product hosts.** For a `P`-space `Ω` and a `Q`-space `Y`, `LC(Ω × Y, k) ⋊ (P × Q) ≅ (LC(Ω, k) ⋊ P) ⊗ (LC(Y, k) ⋊ Q)`.
   So the product host is finitely presented iff both factors are. With `Y = ∂F_d`, a boundary-product host
   `B_Ω ⊗ L_∂` over `Z^2 × F_d` is finitely presented iff `B_Ω` is. By
   `sft-crossed-product-fp-iff-quantum-rigid` (unreviewed), that happens iff `Ω` is a quantum rigid `Z^2`-SFT.
   So the boundary-product lane cannot bypass `free-minimal-z2-sft-is-quantum-rigid`, nor
   `positive-entropy-sft-crossed-products-are-not-fp`.
2. **Leavitt stabilization.** `B ⊗ L_k(1, n)` is finitely presented iff `B` is. Tensoring with Leavitt or
   boundary factors changes growth and `K`-theory but never finite presentation.

**Class killed.** Approaches that pass to a tensor-stabilized host to gain finite presentation.
- **Invariant.** The ascending chain `K_(r,s)` of presentation ideals of `A_r ⊗ C_s`.
- **Failing step.** A finitely generated kernel is some `K_(r,s)`, which forces `A = A_r` and `C = C_s`.

Route: `tensor-product-algebra-fp-iff-factors-fp-proof` (self-contained; folklore in
spirit, recorded here because the graph uses it).
