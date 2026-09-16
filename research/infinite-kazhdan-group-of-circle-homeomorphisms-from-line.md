---
rg: 2
id: infinite-kazhdan-group-of-circle-homeomorphisms-from-line
kind: route
title: Realize an infinite left-orderable Kazhdan group on the line and compactify the line to the circle by one fixed point
target: infinite-kazhdan-group-of-circle-homeomorphisms
requires: [infinite-left-orderable-kazhdan-group, discrete-kazhdan-groups-are-finitely-generated]
artifacts:
  - research/artifacts/kazhdan-circle-group-lift-dichotomy-2026-09-16.md
---

Let `H` be an infinite left-orderable group with property (T), as provided by
`infinite-left-orderable-kazhdan-group`.

1. **Countability.** `H` is finitely generated
   (`discrete-kazhdan-groups-are-finitely-generated`), so it is countable.
2. **Dynamical realization.** A countable left-orderable group embeds in `Homeo_+(R)`.
   The artifact (Lemma 2) gives a complete proof in three steps:
   - *(2a)* Cantor's back-and-forth theorem, proved there.
   - *(2b)* Extension of order automorphisms of `Q` to `Homeo_+(R)` through Dedekind
     cuts.
   - *(2c)* The order `H ×_lex Q` is countable and dense without endpoints, so it is
     order-isomorphic to `Q`. The left action `g·(h,q) = (gh,q)` preserves this order,
     transports to `Aut(Q,<)`, and extends to a homomorphism `ρ : H → Homeo_+(R)`.

     `ρ` is faithful, since `ρ(g)` moves `ψ(1,0)` to `ψ(g,0)`. Here `ψ` is the order
     isomorphism.
3. **From the line to the circle.**
   - Fix an increasing homeomorphism `u : R → (0,1)`, and identify `(0,1)` with
     `S^1 \ {[0]}` through `R → R/Z`.
   - For `F ∈ Homeo_+(R)`, let `F^♮` act as `u F u^{-1}` on `S^1 \ {[0]}` and fix
     `[0]`.
   - Since `u F u^{-1}` is an increasing bijection of `(0,1)`, it maps `(0,δ)` onto some
     `(0,δ')` and `(1-δ,1)` onto some `(1-δ'',1)`. So `F^♮` is continuous at `[0]`.
     With inverse `(F^{-1})^♮`, it is a homeomorphism.
   - `F ↦ F^♮` is an injective homomorphism `Homeo_+(R) → Homeo_+(S^1)`.

So `g ↦ ρ(g)^♮` embeds `H` in `Homeo(S^1)`, and `H` is infinite with property (T). ∎

With `infinite-left-orderable-kazhdan-group-from-circle`, this makes Navas's Questions 2
and 3 equivalent.
