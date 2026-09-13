- **Torsion is spent in characteristic 3; the gate stays OPEN at `<x_0, x_1, s>`** (w7-v-cycle-c3; artifact
  `research/artifacts/p-cycle-tree-rank-models-and-ternary-gate-2026-09-12.md`). Held OPEN until `w3-vf-linear`
  re-derives it.
  - **Finite subgroups.** By the candidate `v-rank-functions-are-trivial-plus-regular-on-cylinder-groups`
    (w7-v-cycle-c2), every rank function on `F_3[V]` is `phi_V rk_aug + (1 - phi_V) rk_reg` on every locally finite
    subgroup. Clopen 3-cycles get `rk((1 - [s])^j) = (1 - phi_V)(3 - j)/3`. Artifact Section 1 is a second derivation
    with different parameters.
  - **No intermediate target.** By convexity (w7-v-cycle-c2's artifact, Section 4.4), this claim is equivalent to
    `phi_V in {0, 1}` for every abstract rank function. Whether the law plus `x_0`, `x_1` conjugation forces
    `phi_V in {0, 1}` is the gate itself.
  - **The law needs a prime other than 3** (`p-cycle-tree-invariance-cannot-force-order-char-law`).
    - **The counter-model.** `rk_2` on `F_3[E_infinity]`, `[g] -> 1 + lambda(g) u` modulo `u^2`, is invariant under
      every injective endomorphism. It has `rk(1 - [g]) = 1/2` and `rk((1 - [g])^2) = 0`, which the law rules out.
    - **First premise broken.** Its induced extension to `E_3 ⋊ <s>` breaks single-element `V`-conjugacy.
  - **Inert.** The finite-subgroup formula holds for the augmentation rank and, on each sofic configuration, for the
    sofic ranks with `phi_V = 0`. So by `sofic-configurations-cannot-force-v-rank-triviality` it can't decide the
    gate.
  - **Where it stops.** I found no identity at `<x_0, x_1, s>` that mixes infinite-order elements with 3-torsion
    beyond single polynomials in `[x]` and matrices over locally finite subgroups. I found no non-augmentation rank
    function. Open:
    - **Abstract reduced quotient.** Is `(rk - phi_V rk_aug)/(1 - phi_V)` always a rank function? If so, the gate is
      equivalent to: no rank function on `F_3[V]` has `phi_V = 0`.
    - **Joint data** on `F_3[B ⋊ <x>]` and `F_3[<x_0, x_1, s>]`.
