---
rg: 2
id: anti-central-ternary-summand-has-no-binary-leavitt-family
kind: claim
title: The canonical trace forbids unital binary Leavitt families in the anti-central ternary summand and fixes the trace of every Cohn defect
distinct_from:
  augmentation-blocks-unital-leavitt-family: that forbids unital binary Leavitt families in matrix rings over integral group rings through the augmentation; this works on the anti-central summand of the ternary group algebra, where no augmentation exists, through the canonical trace instead, and it allows quaternary families.
  ternary-anti-central-summand-has-cohn-family: that is the open request for a unital two-pair Cohn family in S_-; this is an established constraint on such families and a no-go for the stronger binary Leavitt relation.
artifacts:
  - research/artifacts/ternary-anti-central-cohn-reformulation-2026-09-12.md
---

Let `G = L_(F_3)(1,2)^x`, `z = -1`, `S = F_3[G]`, `S_- = F_3[G] / (1 + [z])` with unit
`1_- = 2(1 - [z])`. For a conjugacy class `C` of `G`, let `tau_C` sum the coefficients on `C`, and put
`tau = tau_({1})`. Each `tau_C` is a trace on `S_-`, with `tau(1_-) = 2`.

1. A unital Leavitt family of type `(1, n)` in `S_-` forces `n = 1 mod 3`. In particular `S_-`
   contains no unital binary Leavitt family.
2. The defect idempotent `p` of any unital two-pair Cohn family in `S_-` has `tau(p) = 1`,
   `tau_({z})(p) = -1`, and `tau_C(p) = 0` for every other class.
3. A quaternary family is not excluded, and a unital quaternary Leavitt family contains a two-pair
   Cohn family.

So an exact lift of the binary Leavitt family `(s_i, t_i)` into `S_-` is impossible. An exact lift of
the quaternary family `(s_i s_j, t_j t_i)` is trace-compatible and sufficient.

Proof: Proposition 2.5 of the artifact.
