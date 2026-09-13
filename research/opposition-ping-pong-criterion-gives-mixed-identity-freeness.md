---
rg: 2
id: opposition-ping-pong-criterion-gives-mixed-identity-freeness
kind: claim
title: Proximal elements whose poles are opposite to all their translates by finitely many constants force mixed-identity-freeness
distinct_from:
  rybak-general-type-limit-set-topologically-free-iff-mif: that is Rybak's equivalence for general type actions on hyperbolic spaces, where any two distinct limit points are in general position; this is a ping-pong criterion on any compact space with a symmetric opposition relation, such as the chambers at infinity of a Euclidean building, where distinct chambers need not be opposite.
  fp-simple-kac-moody-lattices-are-mif: that imports Rybak's MIF theorem for simple Kac--Moody groups through a hyperbolic curtain model; this is an abstract criterion meant for groups, like uniform lattices on Euclidean buildings of rank two, that have no rank-one isometries to feed such a model.
---

Let a group `G` act by homeomorphisms on a compact Hausdorff space `Z`, and let
`O ⊆ Z × Z` be a symmetric subset ("opposition"). For `z ∈ Z` put
`O(z) = {y ∈ Z : (y, z) ∈ O}`.

**Definition.** An element `h ∈ G` is *proximal with poles* `(z₊, z₋)` if:

- **(PR1)** `O(z₊)` and `O(z₋)` are open, and each has at least two points;
- **(PR2)** for every compact `K ⊆ O(z₋)` and every open `U ∋ z₊` there is `n₀`
  with `hⁿ(K) ⊆ U` for all `n ≥ n₀`;
- **(PR3)** for every compact `K ⊆ O(z₊)` and every open `U ∋ z₋` there is `n₀`
  with `h⁻ⁿ(K) ⊆ U` for all `n ≥ n₀`.

**Claim.** Suppose:

- **(GP)** for every finite `F ⊆ G ∖ {1}` there is a proximal `h ∈ G` with poles
  `(z₊, z₋)` such that `g·z_s ∈ O(z_t)` for all `g ∈ F` and all
  `s, t ∈ {+, −}`.

Then `G` is mixed-identity-free: for every nontrivial `w ∈ G * ⟨x⟩` there is
`γ ∈ G` with `w(γ) ≠ 1`. Here `w(γ)` is the image of `w` under the
homomorphism `G * ⟨x⟩ → G` that is the identity on `G` and sends `x` to `γ`.

**Remarks.**

1. For `O = {(y, z) : y ≠ z}` on the limit set of a general type action on a
   hyperbolic space, (PR2)–(PR3) is north–south dynamics of a loxodromic
   element and (GP) is the general position used in the (2) ⇒ (1) direction of
   `rybak-general-type-limit-set-topologically-free-iff-mif`.
2. On the chambers at infinity of a Euclidean building with `O` = opposition,
   (GP) with `s = t` asks that each `g ∈ F` map a pole to an opposite chamber.
   An automorphism that maps no chamber to an opposite one (a *domestic*
   automorphism) can never satisfy it.

The argument is the standard ping-pong; no novelty is claimed.

DERIVATION
opposition-ping-pong-mif-criterion-proof
