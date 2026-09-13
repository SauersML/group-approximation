---
rg: 2
id: kim-koberda-lodha-2-prechain-powers-generate-f
kind: claim
title: "Kim–Koberda–Lodha: homeomorphisms of the line supported on a chain of intervals have large powers generating a chain group, so two overlapping bumps give a copy of F"
---

**Source.** S.-H. Kim, T. Koberda and Y. Lodha, *Chain groups of homeomorphisms of
the interval*, arXiv:1610.04099 (v3, 9 Dec 2017), Setting 1.1, the definition of
chain group, and Theorem 1.1.

**Verbatim (pp. 1–2).** "Suppose 𝒥 = {J_1, …, J_n} is a collection of nonempty open
subintervals of ℝ. We call 𝒥 a chain of intervals (or an n–chain of intervals if the
cardinality of 𝒥 is important) if J_i ∩ J_k = ∅ if |i − k| > 1, and if J_i ∩ J_{i+1}
is a proper nonempty subinterval of J_i and J_{i+1} for 1 ≤ i ≤ n − 1."

"Setting 1.1. We let n ≥ 2 and let 𝒥 = {J_1, …, J_n} be a chain of intervals such
that ∂⁻J_i < ∂⁻J_{i+1} for each i < n. We consider a collection of homeomorphisms
𝓕 = {f_1, …, f_n} such that supp f_i = J_i and such that f_i(t) ≥ t for each t ∈ ℝ.
We set G_𝓕 = ⟨𝓕⟩ ≤ Homeo⁺(ℝ)."

"We call the group G = G_𝓕 a prechain group. We say that G is a chain group
(sometimes n–chain group) if, moreover, the group ⟨f_i, f_{i+1}⟩ is isomorphic to
Thompson's group F for each i = 1, 2, …, n − 1."

"Theorem 1.1. If G is a prechain group as in Setting 1.1, then the group
G_N := ⟨f^N | f ∈ 𝓕⟩ ≤ Homeo⁺(ℝ) is a chain group for all sufficiently large N."

**Form used in this graph (n = 2).** If `f, g ∈ Homeo⁺(ℝ)` have `supp f = (a,b)` and
`supp g = (c,d)` with `a < c < b < d`, then `⟨f^{εN}, g^{δN}⟩ ≅ F` for all
sufficiently large `N`, where `ε, δ ∈ {±1}` are chosen with `f^ε(t) ≥ t` and
`g^δ(t) ≥ t` for all `t`. The signs exist: a homeomorphism whose support is one open
interval moves every point of that interval in one direction, since `t ↦ f(t) − t`
is continuous with no zero there, and `f^{-1}` has the same support. An element of
`PL_o(I)`, extended by the identity outside `[0,1]`, is a homeomorphism of `ℝ` with
the same support.

**Scope.** Citation import. The statements were read from pages 1–2 of the arXiv
PDF on 2026-09-13; the proof was not re-derived here. Used by
`two-one-bump-pl-maps-unequal-supports-ea-or-contain-f`.
