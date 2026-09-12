---
rg: 2
id: thompson-v-carries-ternary-nonaugmentation-rank-function
kind: claim
title: The ternary group algebra of Thompson's V carries a Sylvester rank function other than the augmentation rank
refuted_by:
  - thompson-v-ternary-rank-functions-are-augmentation
distinct_from:
  thompson-v-is-sofic: that is Hamming approximability of V, which implies this; this asks only for one non-augmentation Sylvester matrix rank function on F_3[V], which need not come from any matricial approximation.
  binary-leavitt-units-carry-nonaugmentation-rank-function: that is the characteristic-two question for the binary Leavitt units; this is the characteristic-three question for V, which kills every ternary corner witness supported in the signed Thompson group.
artifacts:
  - research/artifacts/signed-thompson-minus-one-gate-is-v-rank-gate-2026-09-12.md
---

**OPEN.** Some Sylvester matrix rank function on `F_3[V]` has `rk(1 - [g]) > 0` for some `g in V`. Since `V` is
simple, such a function then detects every nontrivial element.

**What it gives** (artifact Section 4.4). Pulling back along `phi : E ⋊ V -> V` gives a rank function on
`F_3[E ⋊ V]` moving `z`
(`signed-thompson-z-moving-rank-functions-match-v-rank-functions`). Consequences:
- **No corner witness in `E ⋊ V`.** No `b, c in eps_- F_3[E ⋊ V]` solve `c e_- b = eps_-`
  (`anti-central-rank-models-kill-ternary-corner-witnesses`, with `Γ = E ⋊ V`, which contains `z`, `w` and `d`).
- **The crossed-product target fails.** `odd-measure-crossed-product-unit-below-cylinder-idempotent` is false.
  The swap `w` gives `N(q_[0]) = 1/2` on `B = F_3[E ⋊ V] eps_-`, so `c' q_[0] b' = eps_-` would force
  `1 <= 1/2`.

## Attempts

- **Soficity would do it** (route `thompson-v-ternary-nonaugmentation-rank-function-from-soficity`).
  - Permutation matrices of a sofic approximation give a detecting rank function over `F_3`.
  - Where it stops: soficity of `V` is open (`thompson-v-is-sofic`).
- **Finite-dimensional representations, dead.** `V` has no nontrivial finite-dimensional representation, so no
  single matrix algebra works.
- **Level and HNN models, not reaching `V`.**
  - `level-unit-hnn-extensions-have-anti-central-rank-models` handles single-letter partial conjugations of
    the level unit group.
  - `V`'s multiplication table on depth-changing elements is not of that form, and `V` is not a subgroup of
    the level group.
- **Non-matricial sources.** Nothing specific to `V` is known. `w4-tensor-rankfn` and `w4-rankfn` study
  non-matricial rank functions for the Leavitt units, and anything they build restricts to `V`.
