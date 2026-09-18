---
rg: 2
id: commonly-fixed-letters-compress-to-faithful-actions-proof
kind: route
title: The compressed recursion is the wreath recursion of G read through the run-length classes, and a trivially acting element fixes a dense set of the old Cantor set
target: commonly-fixed-letters-compress-to-faithful-actions
requires:
  - loop-retraction-forces-fp-eventual-section-groups
---

Notation of the claim.

## 1. σ is an endomorphism with eventually periodic powers

Every `g in G` fixes `x`, so `(gh)|_x = g|_{h(x)} h|_x = g|_x h|_x`: `σ` is an endomorphism of `G`, and
`σ(G) = ⟨σ(S)⟩`. By the choice of `p` and `q`, `σ^p = σ^{p+q}` on `S`, hence on `G`
(both are endomorphisms agreeing on generators). So `σ^b = σ^{[b]}` for every `b >= 0`.

## 2. The compressed recursion is a homomorphism into Aut(A^*)

Define, for `g in G`, a permutation `π_g` of `A` and sections by `π_g(y,c) = (σ^c(g)(y), c)` and
`g|_{(y,c)} = σ^c(g)|_y in G`. Each `σ^c(g)` fixes `x`, so it permutes `Y`, and `π_g` is a permutation.
Cocycle rule: `σ^c(gh) = σ^c(g) σ^c(h)`, so
`π_{gh}(y,c) = (σ^c(g)(σ^c(h)(y)), c) = π_g(π_h(y,c))` and
`(gh)|_{(y,c)} = σ^c(g)|_{σ^c(h)(y)} σ^c(h)|_y = g|_{π_h(y,c)} h|_{(y,c)}`.
So `g ↦ (π_g; (g|_a)_{a in A})` is a wreath recursion `G -> G ≀ Sym(A)`, and it defines an action of `G` on `A^*`
by `g(a w) = π_g(a) g|_a(w)`. For `s in S` the sections `σ^c(s)|_y` lie in `S` (sections of states are states,
and `σ(S) ⊆ S`), so the action is given by the finite automaton with state set `S`.

## 3. It is the old action read through run classes

Let `Ω ⊆ X^ω` be the set of points with infinitely many letters from `Y`; it is `G`-invariant and dense. Write
`ξ = x^{b_0} y_0 ξ'` with `ξ' in Ω`. Then `g(ξ) = x^{b_0} σ^{b_0}(g)(y_0 ξ') = x^{b_0} y_0' h(ξ')`, where
`y_0' = σ^{[b_0]}(g)(y_0)` and `h = σ^{[b_0]}(g)|_{y_0} = g|_{(y_0,[b_0])}`. So the map
`κ: Ω -> A^ω`, `x^{b_0} y_0 x^{b_1} y_1 … ↦ (y_0,[b_0])(y_1,[b_1])…`, satisfies `κ(g ξ) = g κ(ξ)`, where `g`
acts on `A^ω` by §2. (`κ` is onto but not injective when some `b_j >= p+q`.)

## 4. Faithfulness

Suppose `g` acts trivially on `A^*`. By §3 the old image of `ξ in Ω` has the same run lengths `b_j` and letters
`y_j' = y_j`, so `g` fixes every point of `Ω`. `Ω` is dense and `g` is continuous, so `g = 1`. ∎

**Remark.** No input from `loop-retraction-forces-fp-eventual-section-groups` is needed beyond the notation.
