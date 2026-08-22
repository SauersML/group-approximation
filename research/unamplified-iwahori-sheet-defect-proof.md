---
rg: 2
id: unamplified-iwahori-sheet-defect-proof
kind: route
title: Reduce the two edge embeddings mod two and count moved sheets
target: unamplified-iwahori-sheets-have-two-thirds-defect
requires: []
---

Reduction modulo `2` identifies

```text
PSL_2(F_2) = S_3
```

and identifies `B` with a point stabilizer.  The matrix

```text
T = [[1,1],[0,1]]
```

is a nonidentity involution modulo `2`, so its permutation of `C/B` is a
transposition.  The corrected dyadic edge presentation in
`iwahori-question-as-square-root-of-parabolic` sends the same abstract edge
generator to `T'^2`.  Since `T'` is also a transposition modulo `2`, `T'^2`
acts trivially on the second three-sheet set.

On `N` disjoint copies, the first permutation therefore moves exactly `2N`
of `3N` points and the second moves none.  Conjugation preserves support, so
for every bijection `u`,

```text
d_Ham(u T^(N) u^(-1), (T'^2)^(N)) = 2N/(3N) = 2/3.
```

This proves the claim.  Notice that it is only a fence against the
unamplified construction: after adding long internal cycles, being a square
has no support-density obstruction.
