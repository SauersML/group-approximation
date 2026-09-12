---
rg: 2
id: predicate-nonscalar-frame-kernel-proof
kind: route
title: Pull allowed target support back through selector-equivariant swaps
target: predicate-preserving-nonscalar-frames-miss-forbidden-source
requires: []
---

For each source character projection `p_a`, selector-equivariance `(PNF2)`
and finite Fourier expansion give

```text
S_i p_a=p_(phi_i(a))^(i) S_i.                          (PNP1)
```

Summing over `a in R` yields

```text
S_i p_R=p_(phi_i(R))^(i)S_i.                           (PNP2)
```

Using `(PNF3)`, `(PNP2)`, and `S_i^*S_i=Q`,

```text
r_i
 =S_i^*q_i p_(phi_i(R))^(i)S_i
 =S_i^*q_iS_i p_R
 =r_i p_R.                                             (PNP3)
```

The same calculation on the other side shows `p_Rr_i=r_i`, while
`r_i=Qr_iQ`.  Hence `r_i<=Qp_R` and `(PNF5)` follows.  On the nonzero range
of `F=Q(1-p_R)`, every `r_i` vanishes, which immediately contradicts any
positive operator lower frame bound `(PNF6)`.

Moreover `(PNP2)` gives

```text
q_iS_iF
 =q_i p_(phi_i(R))^(i) S_i(1-p_R)Q
 =q_iS_i p_R(1-p_R)Q
 =0.                                                    (PNP4)
```

Since `S_i` is isometric on `Q` and `F<=Q`, `(PNP4)` gives

```text
||(1-q_i)S_iF||_2^2=||S_iF||_2^2=||F||_2^2,
```

which is `(PNF7)`.

For the conjugate specialization, normalizing `A` permutes its character
projections.  Predicate preservation says exactly

```text
t_i p_R t_i^(-1)=p_R.
```

Conjugating `q<=p_R` proves `(PNF8)`, and the preceding common-kernel
argument applies with the inclusion/conjugation partial isometries.

