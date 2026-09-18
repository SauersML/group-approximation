---
rg: 2
id: odometer-stable-twists-are-unipotent-mod-two
kind: claim
title: An odometer-stable group of binary tree automorphisms has a twist that is unipotent on the Frattini quotient of its closure, so Fibonacci-type twists are impossible and every such twist fixes a nonzero class mod 2
distinct_from:
  odometer-conjugation-realizes-the-shell-shift: that turns window-zero witnesses of sign −1 into odometer-stable groups of tree automorphisms; this gives the first algebraic necessary condition on such groups, a constraint on the twist from the pro-2 topology.
  window-zero-twists-are-fixed-point-free: that forbids fixed points of the twist in the group; this forces fixed vectors of the twist on a mod-2 quotient, so a realizable twist is fixed-point free in the group but unipotent modulo 2.
  cyclic-input-window-zero-needs-an-automorphism-twist: that excludes a ↦ a^k for Z by counting along the ray; this excludes, among others, every twist whose action on the mod-2 abelianization has no eigenvalue 1.
artifacts:
  - research/artifacts/gq-bh-bh-shell-kazhdan-rigidity-attempt.md
---

**ESTABLISHED** by `odometer-stable-twists-are-unipotent-mod-two-proof` (lane proof, elementary, not independently reviewed, no priority claimed).

## Setting

`T` is the rooted binary tree and `o ∈ Aut(T)` the odometer, as in `odometer-conjugation-realizes-the-shell-shift`. `G ≤ Aut(T)` is finitely generated with `o G o^-1 ⊆ G`, and `psi(g) = o g o^-1`. `Ḡ` is the closure of `G` in the pro-2 group `Aut(T)`, `Φ(Ḡ)` is its Frattini subgroup, and `V = Ḡ/Φ(Ḡ)`. `V` is a finite `F_2`-vector space, because `Ḡ` is topologically finitely generated, and `G` maps onto `V`.

## Statement

1. **Unipotence.** Conjugation by `o` maps `Ḡ` into itself and induces an `F_2`-linear map `psi_V` on `V` whose order is a power of `2`. Hence `(psi_V - 1)^(dim V) = 0`.
2. **A fixed class mod 2.** If `G != 1` then `V != 0`, so `psi_V` fixes a nonzero vector. Concretely, some `g ∈ G` outside the preimage of `Φ(Ḡ)` satisfies `psi(g) ≡ g` mod `Φ(Ḡ)`.
3. **The same holds on finite quotients.** For every open normal subgroup `U` of `Ḡ` with `o U o^-1 ⊆ U`, the map induced by `psi` on the finite `2`-group `Ḡ/U` has `2`-power order.
4. **A test on generators.** Suppose `G = <b_0, …, b_K>` with `psi(b_k) = b_(k+1)` for `k < K` and `psi(b_K) = w(b_0, …, b_K)`. Then `V` is a quotient of `F_2^(K+1)` invariant under the recurrence matrix `M` of `w` mod `2`, and `M` must act unipotently on `V`. If `M` has no eigenvalue `1` over the algebraic closure of `F_2` on any nonzero invariant quotient, then `G = 1`.
   - The Fibonacci twist `b_0 ↦ b_1 ↦ b_0 b_1` has `M = [[0,1],[1,1]]`, of order `3`, and is impossible.
   - The zigzag `D_∞` of `odometer-conjugation-realizes-the-shell-shift` has `M = [[0,1],[1,0]]`, which is unipotent mod `2`, as required.

## Lesson for general BH

Suppose the self-similarity of the shell at infinity is realized inside a profinite group of tree automorphisms. The twist is then conjugation by an element whose `2^m`-th powers tend to `1`. Such a twist is unipotent on every finite characteristic quotient. So the right design principle for shell self-similarity is a twist that is fixed-point free in the group, as `window-zero-twists-are-fixed-point-free` requires, yet unipotent modulo `p`. Twists with hyperbolic abelian behaviour, of Fibonacci or Anosov type, are excluded in every pro-`p` model.

The same argument works for the `p`-adic odometer on the `p`-ary tree, with `2` replaced by `p`. It uses only that the conjugator lies in a pro-`p` group.

## Scope

This is a necessary condition. It gives no construction. Kazhdan inputs are not in scope: simple groups have no faithful action on `T`, since tree automorphism groups are residually finite.
