---
rg: 2
id: eleven-term-lift-radius-four-exhaustion
kind: route
title: Rank the ball translates of A over F2 and ask whether the identity is in their span
target: eleven-term-s0-lift-has-no-radius-four-left-inverse
requires:
  - leavitt-cross-atlas-eleven-term-s0-lift
artifacts:
  - experiments/kaplansky_affine_lift_search.py
  - experiments/kaplansky_joint_lift_search.py
  - research/artifacts/kaplansky-cross-atlas-affine-lift-2026-09-07.md
---

## Proof

Over `F_2` the equation `BA = 1` is linear in the coefficients of `B`.  Write
the ball as `g_1, ..., g_N`; then

```text
B = sum_i c_i g_i,        BA = sum_i c_i (g_i A),
```

so `BA = 1` asks exactly whether the identity element's indicator lies in the
`F_2`-span of the vectors `g_i A`, each of which is the support of the
translate, computed by literal group multiplication and reduced to the
canonical normal form.  Build the augmented matrix over the union of all
supports, run Gaussian elimination with bitset rows, and read off whether the
target reduces to zero.  Elimination over `F_2` is exact and terminating, so a
failure to reduce is a proof of nonexistence **within the spanning set**.

The counts are `795` columns at radius three and `5503` at radius four.  For
the joint system of item 2 the same elimination carries two clause blocks at
once — the convolution rows for `BA = 1` and the evaluation rows for
`evaluation(A) = s_0` — and solves for `A` with `B` fixed.

Two guards make the negative reading honest.  The Leavitt evaluation is used
only to construct `A` and to prove `AB != 1`; it is never used to conclude
`BA = 1` from the quotient, which `direct-finiteness-not-inherited-by-quotients`
forbids.  And the spanning set is the ball, not `Q`, so the conclusion is
scoped to the ball and stated that way in the claim.

Reproducers:

```text
python experiments/kaplansky_affine_lift_search.py \
  --lift-radius 3 --inverse-radius 4 --mandatory atlas4
python experiments/kaplansky_joint_lift_search.py \
  --lift-radius 3 --a-radius 3 --samples 256
```
