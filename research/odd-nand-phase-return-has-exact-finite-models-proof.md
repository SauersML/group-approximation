---
rg: 2
id: odd-nand-phase-return-has-exact-finite-models-proof
kind: route
title: Use the three singleton assignments and amplify their signed permutation action
target: odd-nand-phase-return-has-exact-finite-models
requires:
  - odd-nand-cycle-cancels-separators-to-central-phase
---

On the basis `(ONF2)`, the sign matrices are

```text
X_1=diag(-,+,+),
X_2=diag(+,-,+),
X_3=diag(+,+,-).                                        (ONP1)
```

Thus each pair has the joint sign patterns
`(-,+),(+,-),(+,+)` exactly once and omits `(-,-)`, proving the full
rank-one NAND assertion.

Take

```text
H_1=(23),             H_2=(31),             H_3=(12).  (ONP2)
```

The permutation `H_i` fixes the unique `X_i=-1` vector and swaps the two
vectors in the `X_i=+1` fiber.  Direct evaluation of `(ONP1)--(ONP2)` gives
`(ONF3)` with `J=-I_3`; it is also exactly the local sheet-swap identity from
`nand-sheet-swap-cannot-be-a-pure-central-phase`.  Applying
`odd-nand-cycle-cancels-separators-to-central-phase` for `n=3` yields
`W_C=J`.

Diagonal signs and coordinate permutations generate the finite signed
permutation group, so this is an exact finite group representation, not only
a matrix solution.  Direct sums preserve every relation and `J=-I`, giving
unbounded exact finite dimensions.  The three-case consequence then follows
formally: a defining equality holds in all representations; without it the
displayed models refute finite soundness; and any extra relations separating
the commuting and approximate models are, by `W_C=J`, exactly a non-RU
central-mark gap.
