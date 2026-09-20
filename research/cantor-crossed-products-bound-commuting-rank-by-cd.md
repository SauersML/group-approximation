---
rg: 2
id: cantor-crossed-products-bound-commuting-rank-by-cd
kind: claim
title: If the trivial kΓ-module has a projective resolution of length s, then no matrix ring over LC(X, k) ⋊ Γ contains s+1 commuting algebraically independent elements
distinct_from:
  finite-field-polynomial-growth-hosts-bound-commuting-rank: that bounds commuting rank in gauge-homogeneous, bounded-propagation pieces over finite fields by dimension counting. This bounds it in the whole crossed product, over every field, by cd_k Γ.
  hochschild-dimension-bounds-commuting-independent-families: that uses a finite bimodule resolution of A. This uses a resolution of the trivial kΓ-module and the von Neumann regularity of LC(X, K); the crossed product need not have finite Hochschild dimension.
  f2-z4-embeds-in-z2-sft-boundary-product-hosts: that asks whether F_2[Z^4] embeds in B_Ω ⊗ L_∂. This bound, at s = 3, answers NO; see f2-z4-has-no-embedding-in-z2-sft-boundary-product-hosts.
---

**ESTABLISHED** by `crossed-product-commuting-rank-via-diagonal-induction` (unreviewed).

Let `k` be a field and `Γ` a group whose trivial module `k` has a projective resolution of length `s` over
`kΓ`, that is, `cd_k Γ <= s`. Let `Γ` act by homeomorphisms on a compact Hausdorff totally disconnected space
`X`, and let `A = LC(X, k) ⋊ Γ` be the algebraic crossed product. Then:
- `w.gl.dim(LC(X, K) ⋊ Γ) <= s` for every field `K ⊇ k`;
- for every `r >= 1`, `M_r(A)` has no commuting independent family of size `s + 1`. So `k[x_1, ..., x_(s+1)]`, and
  `k[Z^(s+1)]`, have no injective algebra map into `M_r(A)`, unital or not.

**Instances.**
- The odometer and every Cantor `Z`-system: `s = 1`. At most one independent commuting element. This agrees with
  the evidence recorded in `f2-z4-embeds-in-z2-sft-boundary-product-hosts`.
- `Γ = Z^m`: `s = m`, and it is sharp, since `k[Z^m] ⊆ A` through the canonical units.
- `Γ = Z^2 × F_d`, acting on `Ω × ∂F_d`: `s = 3`. This gives `B_Ω ⊗ L_∂` and the commutative-rank conjecture of
  `f2-z4-embeds-in-z2-sft-boundary-product-hosts`, in its crossed-product form.
- Every Cantor action of a free group: `s = 1`.
