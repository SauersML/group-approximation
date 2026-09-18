---
rg: 2
id: integral-affine-splitting-types-have-finitely-many-tuple-orbits
kind: claim
title: In the twisted integral-affine full group, the global affine symmetries act on halving directions with finitely many orbits on k-tuples, because halving only sees Z_2 mod 2
distinct_from:
  twisted-integral-affine-full-group-is-finitely-presented: that is the open finite-presentation claim; this is one combinatorial input a Stein-Farley proof of it would need, the analogue of the type [A_2] pair-orbit condition.
  finitary-steinberg-extensions-by-oligomorphic-actions-are-fp: that counts orbits of Thompson's F on tuples of coordinates; this counts orbits of the affine group on tuples of halving directions, which are index-2 subgroups rather than coordinates.
---

**ESTABLISHED** (lane proof, not reviewed; elementary).

Let `X = Z_2^D`, and let `Γ_X = (Z^(D) ⋊ GL(Z; D)) ⋊ F` be the group of global affine maps
`x ↦ Mx + b` (finitary integral `M`, finitely supported integral `b`), twisted by
Thompson's `F` permuting `D`. These are exactly the elements of the group `W` of
`twisted-integral-affine-full-group-is-finitely-presented` that are affine on all of `X`.
A **halving direction** is an open subgroup `H ≤ X` of index 2 cut out by a finitely
supported functional: `H = {x : φ(x) ≡ 0 mod 2}` with `0 ≠ φ ∈ F_2^(D)`. It gives the
halving `X = H ⊔ (H + h)`, and each half is carried onto `X` by an element of `W`
(apply some `M ∈ GL(Z; D)` taking `H` to `{x_d even}`, then halve `x_d`). The coordinate
halvings used by Brin–Thompson groups are the case `φ = e_d^*`.

**Claim.**
1. `Γ_X` acts on the set `𝓗` of halving directions through `GL(F_2; D) ⋊ F`, by
   `φ ↦ φ ∘ M^{-1} mod 2` (translations act trivially).
2. For every `k`, `Γ_X` has finitely many orbits on ordered `k`-tuples of distinct
   halving directions. The orbit of `(φ_1, …, φ_k)` is determined by which subsets of
   `{φ_1, …, φ_k}` are linearly dependent over `F_2`.

**Why it matters.** For the untwisted linear action of `E(Z)` on vectors, pairs have
the unbounded invariant `[Z^n : Zv + Zw]` (`twisted-integral-affine-full-group-is-finitely-presented`,
"Obstacle"). That invariant is invisible to halving directions, which only see
`X/2X = F_2^D`. So the natural Stein–Farley complex for `W`, whose simplices are
families of halvings, has the finiteness pattern that Zaremsky's type `[A_2]` condition
gives for `DV_F`: finitely many orbits of pairs of halvings. This removes the obstruction
that kills the vector-action approach. It does not prove the claim: the descending links
and the stabilizers of halving tuples still have to be controlled.

## Proof

1. `M(H) = {x : φ(M^{-1}x) ≡ 0}`, and `M^{-1}` is integral, so reduction mod 2 is compatible.
   A translation by `b ∈ Z^(D)` maps `H` to the coset `H + b`, which is `H` or its
   complement; the halving direction (the subgroup) is unchanged.
2. `SL_n(Z) → SL_n(F_2) = GL_n(F_2)` is onto for every `n`, so `GL(Z; D)` maps onto the
   finitary `GL(F_2; D)`. For finitary `GL(F_2; D)` on the infinite-dimensional space
   `F_2^(D)`, two `k`-tuples with the same linear-dependency pattern are related by a
   finitary linear automorphism: extend a basis of the span of one tuple, match it with
   the other, and fix a complementary finite-codimension subspace. There are finitely
   many dependency patterns on `k` elements. ∎
