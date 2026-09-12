---
rg: 2
id: binary-leavitt-units-carry-nonaugmentation-rank-function
kind: claim
title: The binary group algebra of the Leavitt unit group carries a Sylvester rank function other than the augmentation rank
refuted_by:
  - binary-cyclic-averaging-idempotent-is-full-on-leavitt-units
  - thompson-v-order-three-averaging-idempotent-is-full
distinct_from:
  binary-leavitt-unit-group-is-f2-linear-sofic: that asks for rank-metric approximations of R^x by matrices over F_2; this asks only for one Sylvester matrix rank function on F_2[R^x] other than the augmentation rank, which linear soficity supplies and which need not be matricial.
artifacts:
  - research/artifacts/binary-cyclic-corner-rank-function-dichotomy-2026-09-12.md
---

**OPEN.** Let `R = L_(F_2)(1,2)` and `rk_ε(X) = rank_(F_2)(ε(X))`. There is a Sylvester matrix rank function
`rk` on `F_2[R^x]` with `rk != rk_ε`.

**What it gives.**
- By `simple-group-rank-functions-are-augmentation-or-detecting`, such an `rk` has `rk(1 - [x]) > 0`
  for every `x != 1`.
- So no averaging idempotent of a nontrivial finite subgroup of odd order is full in `F_2[R^x]`
  (artifact Corollary 1.3).
- That refutes `binary-cyclic-averaging-idempotent-is-full-on-leavitt-units` and
  `thompson-v-order-three-averaging-idempotent-is-full`.
- It says nothing directly about Kaplansky pairs: `rk(1 - ba) = 0` is compatible with a detecting `rk`.

**Its negation.** "`rk_ε` is the only Sylvester matrix rank function on `F_2[R^x]`" follows from either
binary averaging target. It implies that every characteristic-two rank model of `R^x` is trivial.

## Attempts

- **Through the evaluation.** Dead: `R` has no Sylvester rank function (artifact 2.1).
- **Homomorphisms to `M_n(D)`, `D` a division ring of characteristic two.** Dead for every `n`. A faithful
  image of the order-`2^k` cylinder cycle would be unipotent, of order at most the least power of two
  `>= n` (artifact 2.2).
- **Monomial and Hamming models.** Dead. They are Hamming models, and a detecting one would make `R^x`
  sofic (`monomial-rank-models-are-hamming-models`, `openai-leavitt-unit-nonsofic`).
- **Linear soficity over `F_2`, or any nontrivial characteristic-two rank model.** Sufficient (route
  `nonaugmentation-rank-function-from-f2-linear-soficity`), and open.
  - The Steinberg rigidity lanes aim to show such models are trivial
    (`leavitt-el3-rank-models-over-finite-fields-are-trivial`).
  - Success there would not refute this claim, because a rank function need not be matricial.
- **What a surviving `rk` must satisfy.**
  - It detects every nontrivial element.
  - It does not come from any `M_n(D)`.
  - On the nine-cylinder group `⟨g, D(g)⟩ ≅ C_3²` it satisfies `rk(1 - e) = 3 rk(e - e_(C_3²))`
    (artifact Section 3).
