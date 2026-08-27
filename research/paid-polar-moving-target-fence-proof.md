---
rg: 2
id: paid-polar-moving-target-fence-proof
kind: route
title: Realize the paid polar on an acute graph orthogonal to the Hecke target
target: paid-polar-bridge-does-not-type-moving-hecke-target
requires:
  - paid-cut-has-moving-hecke-source-or-detector
  - el20-order-seven-heads-force-zero-common-hecke-reducing-cut
---

Put `A=EC_sQ_s=V|A|`.  Then

```text
A^*A=Q_sC_sEC_sQ_s,              AA^*=EC_sQ_sC_sE,
V^*V=supp(A^*A),                  VV^*=supp(AA^*)<=E.  (1)
```

For an ordinary word `a`, before polar correction one knows only

```text
A^*aA=Q_sC_sEaEC_sQ_s.                                (2)
```

On the positive support,

```text
V^*aV=|A|^(-1)A^*aA|A|^(-1).                          (3)
```

The inverse factors are analytic and matrix-dependent.  Thus `(3)` is an
authenticated relative coefficient only after the raw sandwiched Gram
`(2)` has itself been typed and bounded.

For the actual source-to-Hecke-target comparison there is only one inverse:

```text
A^*u_i s^(-1)R_s=Q_sC_sEu_i s^(-1)R_s,
V^*u_i s^(-1)R_s=|A|^(-1)A^*u_i s^(-1)R_s.            (3a)
```

The first line is precisely the ordinary-word-authenticated raw relative
Gram.  Source positivity controls `A^*A`, not `(3a)`, so it supplies no
target incidence.

For the exact model, let `K` be nonzero and take

```text
H=Q_0 directSum Q_1 directSum ... directSum Q_6 directSum E_0,
Q_j isomorphic to K,       E_0 isomorphic to K.        (4)
```

Let `Q,E` project onto `Q_0,E_0`, and let `U` cyclically permute the seven
`Q_j` while fixing `E_0`.  Put

```text
P=UQU^*=Q_1,          u_1=u_2=U,
A_1=J_1=J_2=1,
v_1=u_1,   v_2=u_2A_1,   t_i=J_iv_i=U.                (5)
```

Thus `u_iQu_i^*=P`, both `J_i` reduce `E`, and `t_i^7=1`.

Choose any unitary `W:Q_0->E_0`.  With `c=sqrt(8)/3`, `d=1/3`, let

```text
Lxi=c xi directSum d Wxi,
```

and let `C=LL^*`, extended by zero on `Q_1,...,Q_6`.  Since
`c^2+d^2=1`, `C` is a projection.  Direct block multiplication gives

```text
||(1-Q)C||_op=d=1/3,
ECQ=cd W,
QCEC Q=c^2d^2Q=(8/81)Q.                               (6)
```

Therefore the polar part of `ECQ` is the arbitrary `W` and has full source
`Q` and range `E`.  But `u_iQH=Q_1` is orthogonal to `EH`, so

```text
W^*u_iQ=0.                                             (7)
```

Finally `t_iQH=Q_1` is orthogonal to `QH`, whence

```text
||(1-Q)t_iQ||_2=sqrt(tau(Q)).                          (8)
```

Thus the strict source-incidence branch, full polar support, two literal
order-seven transports, and the forced moving-boundary payment coexist
with zero target Gram and arbitrary polar gauge.  Taking `s=1` proves the
fence; simultaneous conjugation handles any frozen `s`.
