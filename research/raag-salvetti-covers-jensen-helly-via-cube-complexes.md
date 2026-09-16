---
rg: 2
id: raag-salvetti-covers-jensen-helly-via-cube-complexes
kind: route
title: Salvetti covers are CAT(0) cube complexes of cube dimension at most the clique number, so the cube-complex theorem applies
target: raag-salvetti-covers-have-the-jensen-helly-property
requires:
  - cat0-cube-complexes-have-the-jensen-helly-property
artifacts:
  - research/artifacts/zp-cube-complex-jensen-helly-2026-09-16.md
---

Let `Γ` be a finite simplicial graph with clique number `k ≥ 1`, and `G_Γ` the
Cayley graph of `(A_Γ, V(Γ))`.

1. **`G_Γ` is a median graph.** It is the 1-skeleton of the universal cover
   of the Salvetti complex, which is a CAT(0) cube complex (Charney–Davis
   1995). 1-skeleta of CAT(0) cube complexes are median (Chepoi 2000;
   Roller 1998). Both are standard and were not re-fetched here.
2. **Its cube dimension is at most `k`** (artifact §9, self-contained). Take a
   coordinate cube `(g,F)`. Flipping `h ∈ F` gives the neighbour `g a_h` with
   `a_h ∈ V(Γ)^{±1}`.
   - For `h ≠ h'`, the corners `g, g a_h`, the double flip and the flip of `h'`
     form an induced square. Its labels satisfy `abcd = 1`.
   - An exponent-sum homomorphism `A_Γ → Z` forces `c = a^{−1}` and
     `d = b^{−1}`. This is Hulbert–Zaremsky, arXiv:2608.25614v1, Observation 4.2
     ("squares are visible"), read 2026-09-16. So `a_h`, `a_{h'}` commute, and
     they are powers of distinct generators.
   - For distinct non-adjacent generators `u, v`, killing all other generators
     maps `A_Γ` onto the free group `F(u,v)`, where `[u,v] ≠ 1`. So distinct
     commuting generators are adjacent.
   - Hence the generators underlying `{a_h : h ∈ F}` form a clique, and
     `|F| ≤ k`.
3. **Conclusion.** `cat0-cube-complexes-have-the-jensen-helly-property` gives
   the Jensen–Helly property of dimension `k' ≤ k`. That implies dimension
   `k`: Helly number `k'+1` implies Helly number `k+1`, and `k'/2 ≤ k/2`.
   - The realization is the Salvetti cover `|X|` inside the hyperplane box,
     with the coordinate l^1 metric.
   - The definition in `jensen-helly-graphs-have-contractible-rips-complexes`
     accepts any metric space containing `V` isometrically, so this is the
     claimed property.

With `every-raag-is-rips-type-r-via-jensen-helly`, this makes `R_t(A_Γ, V(Γ))`
contractible for every integer `t ≥ k(k+1) − 1`. All links in that chain are
UNREVIEWED.
