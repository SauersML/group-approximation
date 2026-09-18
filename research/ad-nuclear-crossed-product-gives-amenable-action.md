---
rg: 2
id: ad-nuclear-crossed-product-gives-amenable-action
kind: claim
title: "Anantharaman-Delaroche: for a discrete group G acting on a locally compact space X, the action is amenable iff the reduced crossed product C_r^*(X x| G) is nuclear"
---

**ESTABLISHED (import)** through `ad-nuclear-crossed-product-gives-amenable-action-citation`.

Source: C. Anantharaman-Delaroche, *Amenability and exactness for dynamical systems and
their C\*-algebras*, arXiv:math/0005014v2 (Trans. Amer. Math. Soc. 354 (2002)), TeX
source `Edinburgh.tex`. The quotes below are copied from the source. Only the macros are
expanded: `\p(G)` is `P(G)`, `\croi` is `⋊`.

## Setting (verbatim, Section 2)

"A *transformation group* is a left `G`-space `X`, where `X` is a locally compact space,
`G` is a locally compact group and `(x,s) ↦ s.x` is a continuous left action from
`X × G` to `X`." Also: "`P(G)` will be the set of probability measures on `G`, equipped
with the weak\*-topology", with `(s.m)(f) = m(s^{-1}.f)`.

## Definition 2.1 (verbatim)

"We say that the transformation group `(X,G)` (or that the `G`-action on `X`) is
*amenable* if there exists a net `(m_i)_{i∈I}` of continuous maps `x ↦ m^x_i` from `X`
into the space `P(G)` such that `lim_i ‖ s.m^x_i − m_i^{s.x}‖_1 = 0` uniformly on compact
subsets of `X×G`."

## Notation (verbatim, Section 3)

"Let `(X,G)` be a transformation group; the C\*-algebra `C_0(X)` of continuous functions
on `X` vanishing at infinity is a `G`-C\*-algebra, with `s.f(x) = f(s^{-1}.x)` for
`s∈G, x∈X, f∈C_0(X)`. The corresponding crossed products will be denoted by `C^*(X⋊G)`
and `C^*_r(X⋊G)` respectively."

## Theorem 3.4 (verbatim, attributed there to [AD])

"Let `(X,G)` be a transformation group, and consider the following conditions:
(1) `(X,G)` is amenable.
(2) For every `G`-`C_0(X)`-algebra `A`, `C_r^*(G,A) = C^*(G,A)`.
(3) For every nuclear `G`-`C_0(X)`-algebra `A`, `C_r^*(G,A)` is nuclear.
(4) `C_r^*(X⋊G)` is nuclear.
Then (1) ⇒ (2) ⇒ (3) ⇒ (4). Morever (4) ⇒ (1) if `G` is discrete."

## Consequence used downstream

For a countable discrete group `Γ` acting by homeomorphisms on a compact space `Ω`: if the
reduced crossed product `C(Ω)⋊_rΓ` is nuclear, the action is amenable in the sense of
Definition 2.1. By the same theorem, the full and reduced crossed products then coincide.
This is item (4) ⇒ (1) ⇒ (2) with `A = C(Ω)`, not a new statement.

**Verification level.** Definition 2.1, the notation paragraph and the statement of
Theorem 3.4 were read in the TeX source (lines 124-160 and 505-600 of `Edinburgh.tex`).
The proof of Theorem 3.4 was not re-checked. The paper cites it to Anantharaman-Delaroche,
Math. Ann. 279 (1987).
