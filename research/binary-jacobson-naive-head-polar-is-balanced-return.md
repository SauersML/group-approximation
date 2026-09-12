---
rg: 2
id: binary-jacobson-naive-head-polar-is-balanced-return
kind: claim
title: The naive Jacobson head polar is an authenticated balanced raw return
artifacts:
  - research/binary-jacobson-naive-head-polar-proof.md
distinct_from:
  binary-jacobson-balanced-shift-transport-is-xor: that computes conjugation of raw column roots by the balanced shift; this compresses the shift to the marked head cut and computes both support projections of the resulting polar.
  binary-jacobson-constant-q-root-envelope-is-finite: that gives a finite marked model for all constant and head-labelled roots; here only the initial support lies in that envelope, while the final support contains the genuinely raw label SQ.
  binary-jacobson-raw-cycle-selects-common-pi-intertwiner: that asks for a return consuming the full active cycle and intertwining unequal PI degrees; this gives one authenticated raw return but proves it is exactly rank-balanced.
---

**ESTABLISHED.**  Work in the standard rank-five overgroup of
`EL_3(J)`, with `Q=1-ST`, and put

```text
a=a_12=[[S,Q,0],[0,T,0],[0,0,1]],
u=w_12,                    h=a u=[[Q,S,0],[T,0,0],[0,0,1]],
w=x_13(Q).                                                (JNP1)
```

Then `h=h^(-1)` and

```text
Ad(h)w=w.                                                 (JNP2)
```

Moreover, for the second native Pauli pair

```text
X_1=x_14(Q),             Z_1=x_43(1),                    (JNP3)
```

one has

```text
Ad(h)X_1=X_1,            Ad(h)Z_1=Z_1.                   (JNP4)
```

Let `rho` be any finite-dimensional unitary representation of these words
and let

```text
P=(1-rho(w))/2,
P'=rho(u)P rho(u)^*,
P''=rho(h)P' rho(h)^*.
```

The projection `P'` is the negative cut of `x_23(Q)`, while `P''` is the
negative cut of the genuinely raw root `x_13(SQ)`.  All three roots commute
with `w`, so the displayed cuts commute with `P`.  The compressed occurrence

```text
R=P rho(a)P=rho(h)P rho(u)P                              (JNP5)
```

is an exact partial isometry satisfying

```text
R^*R=P P',                 RR^*=P P''.                   (JNP6)
```

Thus `polar(P rho(a)P)=R` on its support.  This is a genuine
occurrence-authenticated `S/T`-bearing rectangular return: its source
projection is the finite-envelope overlap of the head cuts for
`x_13(Q),x_23(Q)`, and its target projection sees `x_13(SQ)`.  But it is
exactly balanced:

```text
rank(PP')=rank(PP'')                                      (JNP7)
```

in every finite-dimensional representation.  Therefore this single polar
cannot itself supply a Hall deficit or a rank-decreasing return.  Any use of
it in the PI route must add a further, occurrence-authenticated incidence
from the remaining raw active-cycle edges; merely sharpening the terminal
rank estimate cannot create the missing excess.

DERIVATION
binary-jacobson-naive-head-polar-proof
