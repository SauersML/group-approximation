---
rg: 2
id: robust-half-period-a2-flip-proof
kind: route
title: Telescope the commutator between the negative and positive half-period faces
target: robust-half-period-a2-flip-pays-simultaneous-doubling
requires: []
---

Conjugating the first word in `(RHF2)` by `V` gives

```text
||[V P V^*,(V Q V^*)^m]+I||_2=alpha_P.                 (RHP1)
```

For unitary pairs, four-letter telescoping gives

```text
||[A,B]-[A',B']||_2
 <=2||A-A'||_2+2||B-B'||_2,                            (RHP2)
```

and power telescoping gives

```text
||(V Q V^*)^m-(Q^2)^m||_2<=m epsilon_Q.                (RHP3)
```

Since `||-I-I||_2=2`, the triangle inequality between `(RHP1)` and the
second word in `(RHF2)` yields

```text
2<=alpha_P+2 epsilon_P+2m epsilon_Q+beta_P.             (RHP4)
```

This is the first inequality in `(RHF3)`.  Interchanging the two root roles
and using power telescoping on `P` gives

```text
2<=alpha_Q+2m epsilon_P+2 epsilon_Q+beta_Q,             (RHP5)
```

which is the second.  Add `(RHP4)--(RHP5)`, take the positive part, and use
`x^2+y^2>=(x+y)^2/2` to obtain `(RHF4)`.



