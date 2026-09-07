---
rg: 2
id: universal-seed-marked-generation-proof
kind: route
title: Compose the four-conjugate swap bound with the four-conjugate corner bound
target: universal-seed-marked-generation-bound-sixteen
requires:
  - signed-swap-normally-generates-elementary-group
  - universal-seed-group-collapses-elementary-groups
  - properly-infinite-unit-rank-two-normal-generator
artifacts:
  - research/artifacts/universal-seed-review-2026-09-07.md
---

## Proof

Take `f` from `universal-seed-group-collapses-elementary-groups`, so
`f = Psi . EL_4(phi)` followed by the block inclusion.

By `signed-swap-normally-generates-elementary-group` in `EL_4(C)`, the
element `e_13(1)` is a product of four conjugates of `a^(+-1)`.  Applying the
homomorphism `f`, its image

```text
D = f(e_13(1)) = diag(1 + S_1T_3, 1)
```

is a product of four conjugates of `f(a)^(+-1)`, the conjugators lying in the
image of `f` and so in `EL_n(R)`.

By `properly-infinite-unit-rank-two-normal-generator` with `v = S_1`,
`w = T_1`, `a = S_3`, `b = T_3`, every elementary generator of `EL_2(R)` is
a product of at most four conjugates of `D^(+-1)`.  Substituting the previous
paragraph gives sixteen conjugates of `f(a)^(+-1)`.

For `n > 2`, each `e_(ij)(r)` lies in the two-coordinate block on `(i,j)`,
which is a copy of `EL_2(R)`; conjugating the whole argument by the
corresponding elementary signed permutation keeps the same count.

Order: `a^4 = 1` in `B` gives `f(a)^4 = 1`, and in `B` itself `a^2 = -I_2 (+) I`
is not the identity because `C` has characteristic zero.
