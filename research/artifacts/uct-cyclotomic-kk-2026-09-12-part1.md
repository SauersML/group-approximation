---
title: Cyclotomic KK-rings of O_2 crossed products by Z_p - UCT-free structure, the Barlak--Li absorption repair, and the K-theoretic fence (lane ex-uct, 2026-09-12, part 1)
---

# Scope

Lane `ex-uct` (EX swarm) on `stw99-problem-ii-nuclear-uct`.  Brief: find a new
approach, or a counterexample candidate with a decisive K-theoretic test, in
the Barlak--Szabó / Barlak--Li picture of `Z_p`-actions on `O_2`.

Read first: the root, the negation node, and the artifacts
`stw-uct-reduction-map-2026-09-11`, `stw-uct-per-prime-cartan-2026-09-12`,
`uct-cartan-obstruction-2026-09-12` and `uct-o2-cyclic-actions-2026-09-12`.

# 1. The new structure theorem (landed fffff736b8)

`order-p-automorphism-kk-cyclotomic-structure`.  Suppose `β^p = id` on a
separable unital `C` and `C ⋊_β Z_p ≃_KK 0`.  Then `KK(C, C)` is a
`Z[ζ_p, 1/p]`-algebra via `ζ_p ↦ [β]`, and `1 − [β]` is a unit.

The mechanism takes three lines:

1. For periodic `β`, `C ⋊_β Z` is isomorphic to the mapping torus of the dual
   automorphism of `C ⋊_β Z_p`.  The injective map `u ↦ z·v` into
   `C(T, C ⋊ Z_p)` has image the `σ`-twisted functions.  So `C ⋊_β Z` is
   contractible.
2. The Pimsner--Voiculescu sequence in `KK(E, −)` makes `1 − β_*` bijective
   for every `E`, so `1 − [β]` is a unit.  Then `N(t) = 0`, because
   `(1 − t)N(t) = 1 − t^p = 0`.
3. In `Z[ζ_p]`, `p = ∏(1 − ζ^k)`, and every `1 − t^k` divides the unit
   `1 − t`.  So `p` is a unit.

Application (`o2-zp-crossed-products-invert-p-in-kk`), through Takai duality:
this holds for `C = O_2 ⋊_α Z_p`, `β = α̂`, and every action `α`.

Corollaries recorded in that node:
- `K_*(C)` and `K^*(C)` are uniquely `p`-divisible;
- the dual action has no invariant or coinvariant classes;
- `[1_C] = 0`;
- at `p = 2`, `[α̂] = −[id_C]`.

# 2. The Barlak--Li absorption step (landed 5042f4822d)

`o2-zp-crossed-products-absorb-uhf-p-without-uct`.  The unital embedding
`C → C ⊗ M_(p^∞)` is a KK-equivalence for every action, and for outer
actions an isomorphism (Kirchberg--Phillips, KK form).

For the passage to the limit, Meyer--Nest (arXiv:math/0312292) Lemma 2.7
(admissibility through completely positive contractions) and Proposition 2.6
(`lim = ho-lim`) give the Milnor sequence.  Multiplication by `p` is bijective,
so `lim^1` vanishes.

This verifies the step that `uct-o2-cyclic-actions-2026-09-12` §3 had marked
UNVERIFIED: Barlak--Li II Theorem 4.16 (i) ⟹ (ii) applies statement (i) to
`O_2 ⋊_α Z_p` before the UCT is known.

# 3. Model tests

* **Cyclic shift on `C^p`.**  The crossed product `M_p` is not contractible,
  and `1 − β_*` kills the diagonal.  The hypothesis is needed.
* **Barlak--Szabó `γ`.**  `K_0 = Z[1/p]^(p−1)` is a rank-one torsion-free
  module over `O = Z[ζ_p, 1/p]`, i.e. a fractional ideal.  Consistent.
* **At `p = 2`.**  `[α̂] = −1` in `KK`, so `α̂` is never approximately inner
  unless `C ≃ 0`.  Consistent with `[1_C] = 0`: a unital automorphism acting as
  `−1` forces `2[1] = 0`, and 2 is invertible.
* **Strongly self-absorbing crossed products.**  Every unital endomorphism of a
  strongly self-absorbing `D` is approximately inner, so `[β] = 1`.  Then
  `1 − [β] = 0` is a unit only when `KK(D, D) = 0`.  So the only strongly
  self-absorbing crossed product `O_2 ⋊_α Z_p` is `O_2`.

# 4. What the theorem does not do

It constrains every action on `O_2` alike, UCT or not.  So it cannot separate a
witness from a bootstrap action.  Part 2 of this artifact determines the full
range of the equivariant K-theoretic invariant on actions with contractible
restriction.  The result is a fence: no K-theoretic signature of any kind
certifies a failure of the UCT here.
