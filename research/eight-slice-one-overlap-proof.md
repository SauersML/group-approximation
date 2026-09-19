---
rg: 2
id: eight-slice-one-overlap-proof
kind: route
title: Compress one unitary between the orthogonal source sum and parent
target: eight-slice-capacity-deficit-is-one-overlap-moment
requires:
  - eight-slice-bookkeeping-symmetrizes-s3-failures
---

Since `C` is a projection and `W` is unitary,

```text
Theta_W=tau((CWS)^*(CWS))=||CWS||_2^2.
```

Also `C<=1`, so `W^*CW<=1` and `Theta_W<=tau(S)`, while cyclicity gives
`Theta_W=tau(CWSW^*C)<=tau(C)`.  Pythagoras for the orthogonal projections
`C,1-C` gives the second identity in `(EOM4)`.  Subtract the two traces in
`(EOM2)` to obtain `(EOM6)`.  Finally expand the fixed finite Fourier
polynomials for `S` and `C` term by term to obtain `(EOM7)`.
