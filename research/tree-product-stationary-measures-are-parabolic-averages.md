---
rg: 2
id: tree-product-stationary-measures-are-parabolic-averages
kind: claim
title: For products of two boundary-2-transitive tree groups, stationary measures are K-averages of unique end-stabilizer-invariant measures
artifacts:
  - research/artifacts/zp-tree-lattice-left-orderability-2026-09-13-part2.md
  - research/artifacts/zp-tree-lattice-left-orderability-2026-09-13-part3.md
---

**ESTABLISHED (unreviewed).** Let `G = G_1 × G_2` with `G_i ≤ Aut(T_i)` closed, non-compact and
2-transitive on `∂T_i`, and let `K = K_1 × K_2` be the stabilizer of a vertex `o`. Let
`P = G_(1,ξ_1) × G_(2,ξ_2)` be the stabilizer of a pair of ends. Let `μ_G` be bi-`K`-invariant, compactly
supported, absolutely continuous and symmetric, with support generating `G`. Assume `G` contains a
torsion-free cocompact lattice `Γ`.

Then for every continuous action of `G` on a compact metrizable space `X` and every `μ_G`-stationary
probability measure `ν` on `X`, there is a unique `P`-invariant probability measure `λ` on `X` with
`ν = ∫_K k_* λ dm_K(k)`.

**Role.** This is Furstenberg's Theorem 3.28 in Witte Morris's exposition of Deroin–Hurtado
(arXiv:2407.09742v1, p. 10), transcribed to products of trees. It was the one structural input still
open in `irreducible-tree-product-lattices-are-not-left-orderable` (gap G4). The uniqueness is used in the
propagation step (Corollaries 3.42 and 4.17) and in Lemma 4.13.

**Proof outline** (artifact part 3; route `tree-product-stationary-measures-are-parabolic-averages-proof`):

1. The walk converges to `∂T_1 × ∂T_2` with the `K`-invariant hitting measure. This uses non-amenability
   of `G_i`, a spectral-radius bound and Borel–Cantelli.
2. That boundary is the Poisson boundary of `(Γ, μ_Γ)`: Kaimanovich's strip criterion,
   arXiv:math/9802132v2, Theorem 6.5(a), applied with quadratically growing strips around flats.
3. Bounded `μ_G`-harmonic functions are Poisson integrals, through the harmonic extension of Witte Morris
   §5.
4. The boundary map gives existence. Uniqueness follows from the martingale characterization of boundary
   maps.

**Trust surface.**

- Statement-level imports, not re-read: Kesten-type spectral gap for non-amenable lcsc groups, and the
  measurable-selection lemma for equivariant maps from a transitive space.
- Witte Morris §5 is an expository sketch.
