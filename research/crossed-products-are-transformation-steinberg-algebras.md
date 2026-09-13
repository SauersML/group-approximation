---
rg: 2
id: crossed-products-are-transformation-steinberg-algebras
kind: claim
title: The algebraic crossed product of a group action on a totally disconnected compact space is the Steinberg algebra of the transformation groupoid
distinct_from:
  minimal-subshift-algebra-is-simple-lef-ring: that proves simplicity and LEF for the shift crossed product over a finite field; this identifies every algebraic crossed product LC(X,k) ⋊ Γ with a Steinberg algebra, so Steinberg-algebra results apply to the Pestov ring.
---

**ESTABLISHED (unreviewed; proof in `crossed-products-are-transformation-steinberg-algebras-proof`).**

**Setting.**
- `Γ` is a discrete group acting by homeomorphisms on a compact totally disconnected Hausdorff space `X`.
- `k` is a commutative unital ring.
- `LC(X,k) ⋊ Γ` is the algebraic skew group ring: finite sums `sum_γ f_γ u_γ` with `f_γ ∈ LC(X,k)` and
  `u_γ f u_γ^(-1) = f o γ^(-1)`.
- `X ⋊ Γ` is the transformation groupoid: arrows `(γ, x)` with source `x`, range `γx`, and product
  `(γ, δx)(δ, x) = (γδ, x)`.

**Statement.** `X ⋊ Γ` is a Hausdorff ample groupoid, and

```text
Ψ : LC(X,k) ⋊ Γ  ->  A_k(X ⋊ Γ),     Ψ(f u_γ)(γ', x) = [γ' = γ] f(γx),
```

is a `k`-algebra isomorphism.

**Instance.** `Γ = Z` acting by the shift `T` on a minimal subshift `X`, with `u f u^(-1) = f o T^(-1)`.
This is the Pestov ring `R = LC(X, F_q) ⋊_T Z`. `X ⋊ Z` is effective and minimal when `X` is infinite and
minimal.
