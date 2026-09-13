---
rg: 2
id: wehrung-countable-refinement-monoids-group-measurable-citation
kind: route
title: Wehrung LNM 2188, Theorem 4.8.7, Proposition 4.7.10 and Theorem 4.7.14
target: wehrung-countable-refinement-monoids-group-measurable
requires: []
---

Source: F. Wehrung, *Refinement monoids, equidecomposability types, and
Boolean inverse semigroups*, Springer LNM 2188 (2017), HAL version
hal-01197354v3 (submitted 17 Aug 2017).  The pages below were read from the
HAL PDF on 2026-09-13.  Page numbers are book pages.

Verbatim, Theorem 4.8.7 (p. 129): "Every countable conical refinement monoid
(M, e) with order-unit is groupoid-measurable. In fact, there exists a
countable fundamental Boolean inverse monoid S such that
(M, e) ≅ (Typ S, typ_S(1))."  The proof begins: "By the countable case of
Theorem 4.6.7, (M, e) is V-measurable, via a normalized V-measure
μ: B → (M, e). By a standard Löwenheim-Skolem type argument, B can be taken
countable. By Theorem 4.8.6, μ is groupoid-induced."

Verbatim, Definition 4.8.1 (p. 128): "A pointed commutative monoid (M, e) is
groupoid-measurable (resp., group-measurable) if there are a unital Boolean
ring B and a groupoid-induced (resp., group-induced) V-measure μ: B → M such
that μ(1) = e."

Verbatim, Proposition 4.7.10 (pp. 124--125): "Let B be a unital Boolean ring,
let (M, e) be a pointed conical refinement monoid, and let μ: B → (M, e) be a
normalized groupoid-induced V-measure. Then each of the following conditions
implies that μ is group-induced: (1) There are a ∈ M and a positive integer m
such that 2a ≤+ e ≤+ ma. (2) For all a, b, c ∈ M, if a + c = b + c ≤+ e, then
there exists d ∈ M such that 2d ≤+ c and a + d = b + d. (3) M is
cancellative."

Verbatim, Theorem 4.7.14 (p. 127): "Let M be a conical refinement monoid, let
B be a Boolean ring, and let μ: B → M be a group-induced V-measure with range
generating M as a submonoid. Then the following statements hold: (1) There
exists a μ-exhaustive action of a group G on B. (2) For any such group
action, there exists a unique monoid homomorphism τ: Z+⟨B⟩//G → M such that
τ([a]_G) = μ(a) for every a ∈ B. Furthermore, τ is a monoid isomorphism."

Verbatim, Definition 4.7.7 (p. 124): "We say that a V-measure μ: B → M is
groupoid-induced (resp., group-induced) if the kernel of μ is ∼gpd_μ (resp.,
≃gp_μ). In particular, μ is groupoid-induced iff for all a, b ∈ B,
μ(a) = μ(b) iff there exists f ∈ Inv(B, μ) such that f(a) = b."  Notation
4.7.4 (p. 123) defines `a ≃gp_μ b` by "decompositions a = ⊕_{i<n} a_i,
b = ⊕_{i<n} b_i, with all b_i = f_i(a_i) where f_i ∈ Aut(B, μ)".

Verbatim, Definition 4.6.1 (p. 119), the V-condition (4.6.1): "Whenever
a, b ∈ M and c ∈ B with μ(c) = a + b, there is a decomposition c = a ⊕ b in B
such that μ(a) = a and μ(b) = b."  A measure is a premeasure that is conical,
"μ^{-1}{0} = {0}".

Verbatim, Section 1.2.1 (p. 7): "The monoid of G-equidecomposability types of
elements of B, denoted by Z+⟨B⟩//G ..., is defined as the commutative monoid
defined by generators [a]_G, where a ∈ B, and relations [∅]_G = 0,
[ga]_G = [a]_G, and [a ⊔ b]_G = [a]_G + [b]_G, where ⊔ denotes disjoint
union."

Verbatim, Proposition 4.8.2(2) (p. 128): "(M, e) is group-measurable iff there
is a group G, acting by automorphisms on a unital Boolean ring B, such that
(M, e) ≅ (Z+⟨B⟩//G, [1]_G)."

Example 4.8.8 (p. 130): "A groupoid-measurable, non group-measurable,
countable conical refinement monoid with order-unit", namely `P` with
generators `epsilon, 1` and relation `epsilon + 1 = 1`.  Theorem 4.8.9
(p. 130): "Every countable conical refinement monoid is group-measurable;
thus it is isomorphic to the type monoid of a fundamental Boolean inverse
semigroup."  Example 4.9.4 (p. 133): "A countable, conical refinement monoid M
with order-unit, such that there is no fundamental Boolean inverse
meet-semigroup S with Typ S ≅ M."

Chapter 7 (pp. 195--198) lists Problems 1--10.  None of them asks for
minimal Cantor realizations or for topologically free realizations.
