---
rg: 2
id: binary-jacobson-balanced-split-pauli-parity-proof
kind: route
title: Factor the conjugated constant A2 pair into its Q and ST branches
target: binary-jacobson-balanced-split-conserves-pauli-parity
requires:
  - opnorm-common-intertwiner-pi-gap-is-sparse-terminal
---

The Jacobson identities

```text
Q^2=Q,       QS=0,       TQ=0,       ST+Q=1,       TS=1
```

give

```text
[[Q,S],[T,0]]^2
 =[[Q^2+ST,QS],[TQ,TS]]
 =[[1,0],[0,1]],                                         (1)
```

so `h` is an involution.  Conjugation of a root entering the `(2,4)` block
right-multiplies its coefficient row by `h`, while conjugation of a root
leaving the block left-multiplies its coefficient column by `h`.  Thus

```text
(1,0)h=(Q,S),              h(1,0)^t=(Q,T)^t,             (2)
```

which is precisely

```text
h x_12(1) h=x_12(Q)x_14(S),
h x_23(1) h=x_23(Q)x_43(T).                              (3)
```

The two factors in each line commute because they share a row or a column.
The cross pairs `x_12(Q),x_43(T)` and `x_14(S),x_23(Q)` are distant and
commute.  The two nontrivial Steinberg commutators are

```text
[x_12(Q),x_23(Q)]=x_13(Q^2)=x_13(Q),
[x_14(S),x_43(T)]=x_13(ST).                              (4)
```

Root additivity and `Q+ST=1` give

```text
x_13(Q)x_13(ST)=x_13(1).                                (5)
```

Conjugation preserves commutators, so `(5)` also agrees with

```text
[hUh,hVh]=h[U,V]h=[U,V]=x_13(1),                        (6)
```

as `h` fixes coordinates `1,3`.

Both centers commute with all four branch roots, so their joint spectral
cuts reduce the displayed finite packet.  On a cut with center signs
`epsilon_Q,epsilon_P`, the standard involution identity

```text
[X,Z]=-1  iff  XZ=-ZX                                    (7)
```

shows that the two target branches are Pauli precisely for their respective
negative signs.  Equations `(5)--(6)` show that the source commutator has
sign `epsilon_Q epsilon_P`.  The three conclusions in the claim follow by
listing the four possible sign pairs.
