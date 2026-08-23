---
rg: 2
id: opnorm-coordinatewise-capacity-diagonal-proof
kind: route
title: Choose a pre-existing challenge rank above the observed coordinate dimension
target: opnorm-coordinatewise-capacity-diagonal
requires: []
---

Assume `(OCD5)` and write `d=dim(U)`. Since `F(N)->infinity`, choose `N` with
`F(N)>d`. The uniform estimate `(OCD2)` gives

```text
max_(q in Q_N)||q(U)-I||_op
 <= C Def_R(U)
 < epsilon_0.
```

Together with the marked separation in `(OCD5)`, the capacity hypothesis
`(OCD3)--(OCD4)` gives `d>=F(N)>d`, impossible.

For the MF corollary, a faithful norm-corona image of a nontrivial `w` has a
positive operator-norm separation along a subsequence. A fixed bounded
power/tensor amplification, chosen after that positive separation is known,
raises it to the prescribed constant `beta` while multiplying the finite
relator defect by only a fixed factor. The defect still tends to zero, so a
coordinate eventually satisfies `(OCD5)`, contradicting the first part.
