---
rg: 2
id: quantum-family-representations-are-exhausted-at-rigidity
kind: claim
title: For a quantum rigid SFT, every quantum-family representation of a local presentation of the V-full group factors through the full group, so these representations cannot detect the gap in P2′
distinct_from:
  fp-v-times-subshift-full-groups-force-quantum-rigidity: that uses the quantum-family representations psi_E to derive quantum rigidity from finite presentation; this shows that once X is quantum rigid, the same representations see nothing beyond F(T), so they cannot prove or refute P2′.
  sft-groupoid-boolean-inverse-monoids-are-finitely-presented: that places the monoid, ring and group presentations in a hierarchy; this is the group-level statement that linear (idempotent-valued) models are exhausted at the ring level.
---

**ESTABLISHED (lane proof, unreviewed; no priority claimed).** Notation as in
`fp-v-times-subshift-full-groups-force-quantum-rigidity` and its route: `Λ` finitely presented, `X ⊆ A^Λ`
a subshift on which `Λ` acts freely, `T = G_V × (Λ ⋉ X)`, and `Σ ⊆ F(T)` a finite generating set
containing every `t_s` and `e_a`.

## Setting

- `Γ_n` is the group presented on `Σ` by all words of length `<= n` that are trivial in `F(T)`.
  `K_n = ker(Γ_n → F(T))`.
- By Tietze, `F(T)` is finitely presented iff `K_n = 1` for some `n`.
- For `D >= R(n)`, Lemma R of the route turns every `D`-quantum family `E` on a space `W_0` into a
  representation `ψ_E : Γ_n → GL(k[C_0] ⊗ k[Λ] ⊗ W_0)`.

## Theorem

Fix `n`, `D >= R(n)` and a field `k`.

1. **Factoring.** `ψ_E` factors through `F(T)` iff the family `E` commutes.
2. **Universal family.** Let `U_D` be the universal `k`-algebra on idempotents `E_a(q)` subject to
   (Q1)–(Q3). Then `ker ψ_(U_D) = ⋂_E ker ψ_E`, the intersection over all `D`-quantum families over `k`.
3. **Exhaustion.** If `X` is `D`-quantum rigid over `k`, then `⋂_E ker ψ_E = K_n`.

So once `X` is rigid, the representations built from quantum families detect exactly the relations of
`F(T)` and nothing more. In particular they cannot decide whether `K_n = 1`, which is P2′.

## Proof

- **(1), "only if."** If `ψ_E` factors through `F(T)`, the relation `[g_1, g_2] = 1` of `F(T)` (two
  translated site-conditioned 3-cycles, Part 1 of the route) holds under `ψ_E` at every pair of
  sites. The route's computation `(H - 1)^2 ⊗ [E_a(p), E_b(q)] = 0`, with `(H - 1)^2 δ_(0^∞) ≠ 0`,
  then gives commutation.
- **(1), "if."** Let `E` commute. Then:
  - **Commutation reaches all patterns.** (Q1) at every site and commutation give
    `M_P = Σ_Q M_Q` over the extensions `Q` of `P` to any larger finite domain.
  - **Non-occurring patterns vanish.** If `P` does not occur in `X`, compactness gives a domain on
    which every extension contains a `B_D`-window not occurring in `X`. So `M_P = 0` by (Q3).
  - **A Clopen(X)-module.** By Stone duality, `P ↦ M_P` is a Boolean homomorphism
    `Clopen(X) → End(W_0)`, making `W_0` a unital `LC(X, k)`-module.
  - **The representation.** `k[Λ] ⊗ W_0` is then the induced `LC(X,k) ⋊ Λ`-module, and
    `k[C_0] ⊗ k[Λ] ⊗ W_0` is a module over the Steinberg algebra
    `k[T] = k[G_V] ⊗ (LC(X, k) ⋊ Λ)`. Each `σ ∈ Σ` acts on it by the indicator of its bisection, and
    that action is the formula defining `ψ_E(σ)`. So `ψ_E` is the restriction of the
    representation `F(T) ⊂ k[T]^×`.
- **(2).** Every `ψ_E` is `ψ_(U_D) ⊗_(U_D) W_0`, because the operators `M_π(z)` in its defining
  formula are left multiplications in `U_D`. So `ker ψ_(U_D) ⊆ ker ψ_E`, and `U_D` is itself a family.
- **(3), the algebra.** Apply rigidity to the regular family on `W_0 = U_D`: the `E_a(q)` commute in
  `U_D`. By the argument in (1), `U_D` is a quotient of `LC(X, k)`. Evaluation at points of `X`
  splits that quotient, so `U_D ≅ LC(X, k)`.
- **(3), the kernel.** By (1), `ψ_(U_D)` is the representation of `F(T)` on
  `k[C_0] ⊗ k[Λ] ⊗ LC(X, k)`.
  - It is faithful on `F(T)`. Evaluating at `x' ∈ X` gives the orbit permutation representation on
    `C_0 × Λx'`.
  - The union of these orbits is dense in `C × X`, and an element of `F(T)` that is the identity on
    a dense set is trivial.
  - So `ker ψ_(U_D) = K_n`. `∎`

## Lesson for general BH

The quantum-family method, the only group-side obstruction technique on main that reads the
dynamics, is exactly the linearization of P2′.
- **Before rigidity.** It detects every non-rigid SFT (walls, golden–silver, positive entropy).
- **At rigidity.** It is exhausted: the linear models of the local relations are already the true
  models.
- **Where a proof of P2′ has to come from.** It must control group relations that are not
  consequences of linear idempotent relations. That calls for a genuinely combinatorial or
  topological argument, such as Stein–Farley connectivity or rewriting of cone partitions. No
  further representation theory of this kind helps.
- **What a refutation would need.** A rigid `X` with non-fp `F(T)` would need a group-theoretic
  witness invisible to every quantum family: a "non-linear quantum family".
