---
rg: 2
id: cantor-crossed-hosts-are-closed-under-boundary-products
kind: claim
title: Tensoring a finitely presented central simple Cantor crossed product with the free-group boundary algebra gives another such host, over P × F_d, with no unital rank model
distinct_from:
  decidable-group-algebras-have-fp-cantor-crossed-hosts: that asks for hosts containing every decidable group algebra; this proves that the class of valid hosts is closed under X ↦ X × ∂F_d, P ↦ P × F_d, with no embedding claim.
  boundary-crossed-product-is-a-leavitt-path-algebra: that identifies the single algebra LC(∂F_d, k) ⋊ F_d; this tensors it with an arbitrary valid host and proves that finite presentation, simplicity, centre, torsion-freeness and FJCw of the acting group all survive.
  amenable-minimal-crossed-products-have-faithful-rank-models: that gives rank models for every amenable minimal host, forcing linear soficity; this produces non-amenable hosts containing any given host unitally that admit no unital rank model at all.
  takesaki-simple-minimal-tensor-simplicity: that is simplicity of minimal C-star tensor products; this is the purely algebraic statement that a central simple algebra tensor a simple algebra is simple, used for crossed products over any field.
artifacts:
  - research/artifacts/cantor-crossed-host-boundary-products-2026-09-17.md
---

**ESTABLISHED (unreviewed; imports Wegner arXiv:1308.2432 verbatim).** Let `k`
be a field. Call `(P, X)` a **valid host** if all of the following hold:
- `P` is torsion-free and satisfies FJCw;
- `X` is a nonempty compact totally disconnected Hausdorff `P`-space;
- `B = LC(X, k) ⋊ P` is finitely presented, simple, and has centre `k`.

Let `(P, X)` be a valid host, let `d >= 2`, and put `L_∂ = LC(∂F_d, k) ⋊ F_d`.

1. `LC(X × ∂F_d, k) ⋊ (P × F_d) ≅ B ⊗_k L_∂`.
2. `(P × F_d, X × ∂F_d)` is a valid host.
3. `B ⊗ L_∂` has no unital homomorphism into any rank ultraproduct of matrix
   algebras.
4. `B ⊗ 1 ⊆ B ⊗ L_∂` unitally, so every unital embedding into `B` persists.

FJCw implies the Farrell–Jones hypothesis of
`cantor-crossed-product-leavitt-tensors-are-k-trivial` (take `F = 1` in the definition of FJCw). So
valid hosts meet every condition of `decidable-group-algebras-have-fp-cantor-crossed-hosts` except
the embedding. Instances: `P = Z^d` and every CAT(0)-group.

**Why it matters.**
- **Attempts 2 and 3 of the target.** The linear-soficity gate there comes from a unital rank model
  of the host. Part 3 shows that hosts over `Z^2 × F_d` have no such model.
  - So the target does not, through any argument in the graph, force decidable groups to be
    `F_2`-linear sofic. Only its amenable case does.
- **Attempt 6.** `Z^2 × F_d` is finitely presented and not free. Its SFTs `Ω × ∂F_d` are exactly as
  hard as `Ω`.
  - `minimal-z2-sfts-have-no-uniform-language-time-bound` gives arbitrarily hard minimal `Ω`. So
    the complexity kill of free-group hosts does not extend to this family.
- The resulting reduction is route
  `cantor-crossed-hosts-via-boundary-products-of-z2-sft-hosts`.

DERIVATION
cantor-crossed-hosts-are-closed-under-boundary-products-proof
