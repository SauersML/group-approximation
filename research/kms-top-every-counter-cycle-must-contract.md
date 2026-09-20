---
rg: 2
id: kms-top-every-counter-cycle-must-contract
kind: claim
title: For K >= 2, a faithful transitive self-similar action of the KMS top B_K whose renormalization has product Frobenius–Möbius form must contract on every cycle of the counter permutation; so partial contraction (one contracting cycle for faithfulness, the machine's counters on non-contracting cycles) is impossible on the top
distinct_from:
  kms-lift-must-mix-top-core-into-configurations: its Theorem M finds a core when no cycle contracts; this finds one as soon as a single cycle fails to contract, by a principal ideal built from that cycle's variables only, which is Theorem M strengthened.
  kms-top-renormalizations-must-contract: that proves the uniform single-cycle case; this is the general product case.
  kms-tops-embed-in-fp-self-similar-metabelian-groups: the Kochloukova–Sidki action has one cycle, and it contracts, so it is consistent with this.
---

**ESTABLISHED (lane bh-kd2p, 2026-09-19; lane proof, not independently reviewed).** This answers the partial-contraction question for `K = 2` and for all `K ≥ 2`, in the product Frobenius–Möbius class.

## Statement

Use the setting and the product Frobenius–Möbius hypothesis of Theorem M in
`kms-lift-must-mix-top-core-into-configurations`: exponents `e_i`, shifts `j_i`, a permutation `π`, and Möbius
isomorphisms `σ_i` over `F_p`. Suppose some cycle `C` of `π` has `Σ_{i∈C} j_i ≥ 0`. Then `f` is not simple.

So in a faithful action, **every** cycle satisfies `Σ_{i∈C} j_i < 0`.

## Proof

1. **Weights on `C` alone.** Choose `w_i ≥ e_i` for `i ∈ C` with `w_{π(i)} ≤ w_i + j_i`. This is possible
   because `Σ_C j ≥ 0`.
2. **A principal ideal in `C`'s variables.**
   - Let `Z` be the support of the finite-codimension ideal `M'' = ⋂_{u∈U/U_H} uM ⊆ M`, so that
     `M'' ⊇ ∏_{z∈Z} 𝔪_z^{N'}`.
   - Let `Z_0 ⊂ P^1(F_{p^r}) \ {0, 1, ∞}` contain every coordinate of every point of `Z`. It is stable under
     Möbius maps over `F_p`.
   - Put `h^{(i)} = ∏_{c∈Z_0} (s_i − c)^{N'}` and `h̃ = ∏_{i∈C} (h^{(i)})^{p^{w_i}}`. Then `h̃ ∈ S`, since
     `w_i ≥ e_i`.
3. **It lies in the domain.** Fix `z ∈ Z` and some `i ∈ C`. `h̃` has the factor `(s_i − z_i)^{N'}`, which lies
   in `𝔪_z^{N'}`. So `h̃ ∈ ⋂_z 𝔪_z^{N'}`, and `h̃R ⊆ M'' ⊆ M`.
4. **It is invariant.**
   - `σ_i(s_i − c) = μ_i(s_{π(i)}) − c` is a unit times `s_{π(i)} − μ_i^{-1}(c)`, since its pole lies over
     `{0, 1, ∞}`. So `σ_i(h^{(i)})` is a unit times `h^{(π(i))}`.
   - Hence `ψ̃(h̃) = ∏_{i∈C} Frob^{w_i + j_i}(σ_i h^{(i)})`, which is a unit times
     `∏_{i∈C} (h^{(π(i))})^{p^{w_i + j_i}}`.
   - Since `w_i + j_i ≥ w_{π(i)}` and `π` permutes `C`, this is divisible by `h̃`.
   - By the Hartogs extension `f̂` (valid because `K ≥ 2`), `f(h̃ r) = ψ̃(h̃) f̂(r) ∈ h̃R` for all `r ∈ R`.
5. **Conclusion.** `h̃R` is a nonzero ideal, hence normal, lies in `M`, and satisfies `f(h̃R) ⊆ h̃R`. So it lies
   in the `f`-core. ∎

**Why `K = 1` escapes.** Step 4 uses the Hartogs extension, which needs `K ≥ 2`. For `K = 1`, division by
`(s − c)` has a pole, and bh-free-25's one-variable action is faithful with `j = 0`.

## Consequences for KD2_p

- **The smallest case, `K = 2`, answers the question.**
  - With `π = id`, both fixed points must contract, so the second counter cannot be isometric.
  - With `π = (1 2)`, there is one cycle, which must contract in total.
  - So the hard counters cannot live on non-contracting cycles of the top.
- **Where the machine's counters live.** They are the `a_i` of the one-variable factors `B_i`. There isometric
  renormalizations such as division by `(a_i − c)` are allowed, as the `K = 1` case above shows. But G6 ties the
  `a_i` to the `ã_i` of `B_0` on the `x_{q_j}`, and the `ã_i` must all contract.
  - A top-preserving lift would need `F(a_i)` (isometric) and `F(ã_i)` (contracting) to act identically on
    `F(x_{q_j})`. That is a necessary condition, not a theorem.
  - For example, it would force `F(x_{q_j})` into the part of `T` fixed by both actions.
- **So the live route is Part D of `kms-lift-must-mix-top-core-into-configurations`.** It needs a lift that does
  not preserve `B_0`, absorbing `B_0`'s core into `T_0`.

## Lesson

**On a multi-variable lamp ring every counter cycle must contract. Faithfulness cannot be bought on one cycle
and hardness kept on another.** The Hartogs extension turns any non-contracting cycle into a principal invariant
ideal.
