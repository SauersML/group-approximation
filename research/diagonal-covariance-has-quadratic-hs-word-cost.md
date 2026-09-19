---
rg: 2
id: diagonal-covariance-has-quadratic-hs-word-cost
kind: claim
title: Diagonal shift covariance propagates to level n with only quadratic Hilbert--Schmidt cost
---

Let `t,U,z` be unitaries in a normalized matrix algebra and put
`c=tU^(-1)`. If

```text
epsilon_0=||[t,U]-I||_2,
epsilon_z=||[c,z]-I||_2,
```

then for every `n>=1`,

```text
||t^n z t^(-n)-U^n z U^(-n)||_2
 <= 4 n^2 epsilon_0+n epsilon_z.                         (DCH1)
```

Consequently the finite diagonal-covariance presentation supplies all shifted
Fanizza/packet input identifications with polynomial certificate cost. This
is compatible with the exponentially weighted contractive ladder.

