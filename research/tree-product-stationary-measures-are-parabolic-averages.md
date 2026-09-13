---
rg: 2
id: tree-product-stationary-measures-are-parabolic-averages
kind: claim
title: For products of two boundary-2-transitive tree groups, stationary measures are K-averages of unique end-stabilizer-invariant measures
artifacts:
  - research/artifacts/zp-tree-lattice-left-orderability-2026-09-13-part2.md
---

**OPEN.** Let `G = G_1 × G_2` with `G_i ≤ Aut(T_i)` closed and 2-transitive on `∂T_i`, and let
`K = K_1 × K_2` be the stabilizer of a vertex `o`. Let `P = G_(1,ξ_1) × G_(2,ξ_2)` be the stabilizer of a
pair of ends. Let `μ_G = μ_1 ⊗ μ_2` with each `μ_i` bi-`K_i`-invariant, compactly supported, absolutely
continuous, symmetric, with `K_i ⊆ supp μ_i` and support generating `G_i`.

Then for every continuous action of `G` on a compact metrizable space `X` and every `μ_G`-stationary
probability measure `ν` on `X`, there is a unique `P`-invariant probability measure `λ` on `X` with
`ν = ∫_K k_* λ dm_K(k)`.

**Role.** This is Furstenberg's Theorem 3.28 in Witte Morris's exposition of Deroin–Hurtado
(arXiv:2407.09742v1, p. 10), transcribed to products of trees. It is the one structural input still open
in `irreducible-tree-product-lattices-are-not-left-orderable`. The uniqueness is used in the propagation
step (Corollaries 3.42 and 4.17) and in Lemma 4.13.

## Attempts

- (z1-22-lo-simple-bm, 2026-09-13) **Plan via the Poisson boundary** (artifact part 2, §3).
  - The martingale limit `β(ω) = lim (g_1 ⋯ g_n)_* ν` exists.
  - Harmonic functions are left `K`-invariant (Witte Morris, Lemma 5.2), so the question is the Poisson
    boundary of a product of two independent isotropic random walks on bi-regular trees.
  - If that boundary is `∂T_1 × ∂T_2` with the `K`-invariant measure, `β` factors through `G/P`, and
    `λ = β(eP)` gives existence. Uniqueness follows from the `μ_G`-boundary property.
- **Where it stands.** Each ingredient is classical, but none is verified here from a source:
  - the Poisson boundary of an isotropic finite-range random walk on a tree is its space of ends;
  - the Poisson boundary of a product measure is the product of the Poisson boundaries;
  - the passage from those to the decomposition for non-algebraic `G`.
