---
rg: 2
id: two-grading-cz-balanced-absorber-proof
kind: route
title: Balance the CZ-twisted spectrum and let the Julia reflection intertwine the two blocks
target: two-grading-cz-gauge-has-a-balanced-intertwiner-absorber
requires:
  - controlled-pauli-corner-has-clifford-groupification
---

Tensoring the `(3,1)` sign multiplicities of `C` with the balanced `(m,m)`
sign multiplicities of `V` gives

```text
mult_(+1)(C tensor V)=3m+m=4m,
mult_(-1)(C tensor V)=3m+m=4m.                         (TGA1)
```

The same multiplicities for `I_4 tensor V` are `(4m,4m)`, proving unitary
equivalence and supplying `U`. The block formula `(TGC3)` immediately gives
`j^2=1` and `zjz=-j`, hence `zjzj=-I`. The intertwining equation
`UR_+=R_-U` and its adjoint are exactly the two off-diagonal blocks of
`Rj=jR`, proving `(TGC4)`.

The negative-to-positive block of `j` is `U^*`, so

```text
(Q U^*)(Q U^*)^*=Q.                                   (TGA2)
```

The negative eigenspace of controlled-Z has rank one in dimension four;
therefore `tr_(H_+)(Q)=1/4`, proving `(TGC6)`. No choice of `U` changes this
calculation.
---
