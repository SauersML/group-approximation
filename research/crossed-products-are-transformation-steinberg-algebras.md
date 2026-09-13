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

**Credit (prior art).** Beuter–Gonçalves, *The interplay between Steinberg algebras and partial skew rings*, J. Algebra 497 (2018) 337–362, arXiv:1706.00127, Theorem `theorisomortransfgrou` (TeX l.442–444): partial skew group rings `L_c(X) ⋊_α G` over locally compact totally disconnected Hausdorff `X` are isomorphic to `A_R(G ⋉_θ X)`. The source itself attributes the result to folklore (l.394). This node is its global-action, compact case. Citation route: `crossed-products-are-transformation-steinberg-algebras-citation`. The lane's proof stays as a second route. Flagged PRIOR by un-novelty (514b76e752).

**Review (un-verify-3, 2026-09-13): PASS.** Re-derived: sheetwise bijectivity (`f ↦ f∘γ`), compact support equals finiteness of the sum, the convolution identity `(F*G)(γδ,x) = f(γδx)g(δx) = Ψ(f·(g∘γ^(-1))u_(γδ))(γδ,x)`, the unit, and effectiveness from topological freeness. The Beuter–Gonçalves statement matches the arXiv TeX verbatim. `research/artifacts/un-review3-2026-09-13-part1.md` §11.
