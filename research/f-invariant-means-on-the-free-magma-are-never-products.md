---
rg: 2
id: f-invariant-means-on-the-free-magma-are-never-products
kind: claim
title: No mean on the free magma that is invariant under Thompson's F re-association is a convolution product, and no mean solves a bookend term equation
distinct_from:
  free-magma-carries-an-idempotent-finitely-additive-measure: that asks for an idempotent mean (Moore's withdrawn Theorem 1.2); this proves the idempotent case false as the k=2 instance of part (B), and in part (A) proves that no F-invariant mean has product form at all, whatever the two factors are.
  moore-ramsey-criterion-for-amenability: that is Moore's finitary Ramsey equivalence for amenability, which is untouched here; this is about the infinitary mean-on-magma formulation of arXiv:1209.2063.
  thompson-f-finite-state-flows-cannot-prove-nonamenability: that uses idempotent state measures of finite automata to kill non-amenability certificates; this proves that the infinite free magma has no idempotent or product-form invariant mean, killing product-form amenability certificates.
  thompson-f-amenable-iff-dyadic-action-extensively-amenable: that is a different reformulation of amenability of F; this constrains only means on the free magma under the partial re-association action.
invalidates:
  - thompson-f-amenable-via-idempotent-magma-measure
artifacts:
  - experiments/free-magma-product-means-2026-09-17/check_product_mean_identities.py
  - experiments/free-magma-product-means-2026-09-17/output.txt
---

**ESTABLISHED (direct proof, unreviewed).** Let `T` be the free magma on one generator `1`, with operation `*`. A
*mean* is a finitely additive probability measure on all subsets of `T`. For means `μ, ν` put
`μ*ν(f) = ∫(∫ f(s*t) dν(t)) dμ(s)`, which is the convolution of `free-magma-carries-an-idempotent-finitely-additive-measure`
and of Moore, arXiv:1807.05469. The generators of `F` act partially on `T` by `x_1((a*b)*c) = a*(b*c)` and
`x_2(s*w) = s*x_1(w)`. A mean `ν` is *F-invariant* in Moore's sense when `ν(dom x_1 ∩ dom x_2) = 1` and
`ν(x_i·Z) = ν(Z)` for `i = 1, 2` and every `Z ⊆ T`. Moore states that `F` is amenable if and only if such a `ν` exists.

- **(A) Product kill.** No F-invariant mean is of the form `μ*β`, for any means `μ, β`.
- **(B) Bookend kill.** Let `w(y_1, …, y_k)` be any binary term with `k ≥ 2` leaves. Then no mean `ν` satisfies
  `ν = w(ν, α_2, …, α_(k−1), ν)`, whatever the means `α_2, …, α_(k−1)` in the middle leaves. The case `w = y_1*y_2`
  is Moore's theorem that idempotent means do not exist (arXiv:1807.05469, Section 2).

**Consequences.**
- The route `thompson-f-amenable-via-idempotent-magma-measure` is invalidated: its prerequisite is the case `k = 2`
  of (B).
- Every *nonassociative Ellis lemma* of fixed-point type dies with it. Examples are `ν = (ν*ν)*ν`, `ν = ν*(α*ν)`,
  and any system of such equations whose first and last leaves carry `ν`.
- (A) goes further. It kills every proof of amenability of `F` that builds the invariant mean as a convolution
  product. That covers idempotents, where Moore's Theorem 3.3 would have given invariance. It also covers fixed
  points `ν = ν*β` of the continuous affine map `R_β`, which exist for every `β` by Markov–Kakutani, and fixed
  points `ν = α*ν`.
- If `F` is amenable, then in every invariant mean the left and right subtrees of the root are *dependent*: the
  mean on `T*T ≅ T×T` is never an iterated product.
- *Invariant:* the right marginal `ρ = r_*μ` of the left factor, where `r(a*b) = b`.
- *Where every member dies:* `x_1`-invariance forces `β = ρ*β`. Then `x_2`-invariance makes `β` itself
  `x_1`-invariant, and together they force `ρ*ρ = ρ`. At that point Moore's self-referential set `Z` gives
  `ρ(Z) = ∫ (1−ρ(Z))^(#a) dρ(a) = 1_(ρ(Z)=0)`, and this equation has no solution.

**Boundary (what survives).** One-sided fixed points exist. For every `β`, `R_β : μ ↦ μ*β` is a weak*-continuous
affine self-map of the compact convex set of means, so `ν = ν*β` has solutions. So (B) is sharp: the kill needs
`ν` in both the first and the last leaf. What (A) leaves open is exactly this: F-invariant means that are not
products. These are the means that amenability of `F` is equivalent to, so (A) is a restriction on the witness,
not a statement about the root.

Proof: route `f-invariant-means-on-the-free-magma-are-never-products-proof`.

## Attempts

- **2026-09-17 (swarm-0917-w7-w7-f-break, belief breaker).** Found while auditing the ⚑ last-missing hole
  `free-magma-carries-an-idempotent-finitely-additive-measure`. The frontier listed it as live, but it is false by
  Moore, arXiv:1807.05469 (Canad. Math. Bull. 2019), which the graph already quoted in
  `research/artifacts/thompson-f-monomial-doubling-2026-09-13.md`. Lane `swarm-0917-w7-w7-f-last1` holds the
  lease for importing that refutation onto the hole itself.
  - This node proves the refutation from scratch, generalizes it to bookend terms (B), and then asks the question
    that matters for the root: can *any* invariant mean on `T` be produced by the product structure that
    Theorem 3.3 exploits? Part (A) answers no.
  - Not covered: F-invariant means obtained as weak* limits of non-product means. A Følner-type construction on
    `T` gives such means whenever `F` is amenable.
