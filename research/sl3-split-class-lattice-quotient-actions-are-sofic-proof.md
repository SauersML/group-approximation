---
rg: 2
id: sl3-split-class-lattice-quotient-actions-are-sofic-proof
kind: route
title: Conjugate into the class of SL3(Z), then alternate coupling duality, restriction to a common finite-index subgroup, and passage to factors
target: sl3-split-class-lattice-quotient-actions-are-sofic
requires:
  - sl3z-lattice-space-action-is-sofic
  - sofic-free-actions-are-soe-invariant
  - paunescu-sofic-action-class-permanence
---

Write `Γ = SL_3(Z)` and `X(Γ_1, Γ_2)` for the action `Γ_1 ↷ G/Γ_2`.

**Tools.**

* **(F) Factors.** If `Γ_1 ↷ X` is sofic and `X → Y` is an equivariant, measure-preserving factor map,
  then `Γ_1 ↷ Y` is sofic. Indeed `L^∞(Y) ⋊ Γ_1 ⊆ L^∞(X) ⋊ Γ_1` is a trace-preserving inclusion that
  sends `L^∞(Y)` into `L^∞(X)` and `u_g` to `u_g`, so a sofic embedding restricts to one.
* **(R) Restriction.** If `Γ_1 ↷ X` is sofic and `Γ' <= Γ_1`, then `Γ' ↷ X` is sofic, by restricting
  the embedding to `L^∞(X) ⋊ Γ'`.
* **(D) Duality.** Every `X(Γ_1, Γ_2)` is essentially free. `γ != 1` fixes `gΓ_2` iff
  `g^(−1)γg ∈ Γ_2 ∖ {1}`, and for `δ != 1` the set `{g : γg = gδ}` is empty or a coset of the proper
  centralizer of `δ` (`G` has trivial center), which is Haar-null. Let `Γ_1 × Γ_2` act on `Ω = G` by
  `(γ_1, γ_2)·g = γ_1 g γ_2^(−1)`, and pick finite-measure Borel fundamental domains `D_2` for the right
  action of `Γ_2` and `D_1` for the left action of `Γ_1`. The orbit relation `E` restricts on
  `D_2 ≅ G/Γ_2` to the orbit relation of `X(Γ_1, Γ_2)`: `d, d' ∈ D_2` are related iff
  `γ_1 dΓ_2 = d'Γ_2`. On `D_1 ≅ Γ_1\G` it restricts to the orbit relation of `Γ_2 ↷ Γ_1\G`, which
  `Γ_1 g ↦ g^(−1)Γ_1` makes isomorphic to `X(Γ_2, Γ_1)`. Both sets meet almost every `E`-class. By
  part 2 of `sofic-free-actions-are-soe-invariant`, `X(Γ_1, Γ_2)` is sofic iff `X(Γ_2, Γ_1)` is.
* **(C) Conjugation.** For `h, k ∈ G`, the map `xΓ_2 ↦ h^(−1)xk·(k^(−1)Γ_2k)` is well defined, sends
  Haar probability to Haar probability, and intertwines `X(Γ_1, Γ_2)` with
  `X(h^(−1)Γ_1h, k^(−1)Γ_2k)` along `γ ↦ h^(−1)γh`. So soficity is unchanged.

**Proof.** By (C) we may assume that `Γ_1` and `Γ_2` are commensurable with `Γ` itself. Put
`Γ_0 = Γ ∩ Γ_1 ∩ Γ_2`, which has finite index in all three.

1. `X(Γ, Γ)` is sofic, by `sl3z-lattice-space-action-is-sofic` with `n = 3`.
2. `X(Γ_0, Γ)` is sofic by (R).
3. `X(Γ, Γ_0)` is sofic by (D).
4. `X(Γ_0, Γ_0)` is sofic by (R).
5. `X(Γ_0, Γ_1)` is sofic by (F), through `G/Γ_0 → G/Γ_1`.
6. `X(Γ_1, Γ_0)` is sofic by (D).
7. `X(Γ_1, Γ_2)` is sofic by (F), through `G/Γ_0 → G/Γ_2`. ∎

No step creates finite orbits or uses equidistribution beyond step 1. The whole commensurability class
inherits soficity from the one Hecke theorem.
