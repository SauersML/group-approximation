---
rg: 2
id: sl3-rank-one-denominator-self-commutator-removes-target-phase
kind: claim
title: One rank-one denominator identity removes the target projective phase quantitatively
distinct_from:
  projective-transfer-equals-rcc-for-perfect-pairs: that kills a limiting scalar character by perfectness of the whole ambient group; this gives a finite-dimensional dimension-free estimate from one explicit rank-one denominator decomposition, before taking an ultraproduct.
  projective-trace-square-transfer-for-sl3-pair: that must prove the denominator commutator is projectively scalar; this only upgrades projective scalarity to ordinary closeness to the identity and does not prove the missing trace-square transfer.
  arithmetic-leak-commutator-localizes-in-overlap-commutant: that places the denominator commutator in a finite-index overlap commutant; this instead expresses it, up to bounded defect, as a conjugate of its own commutator with one half-integral root.
---

Work in the `(1,3)` copy of `SL_2` inside

```text
A=SL_3(Z[1/2]),       Lambda=SL_3(Z),
h=diag(2,1,1/2).
```

Put

```text
x(r)=I+rE_13,    y(r)=I+rE_31,
X=x(2),          Y=y(-2),
C=x(-1)y(1)x(-1).
```

For a unitary representation write `H=rho(h)`, use the same letters for
the represented integral elements, and set

```text
Z=H Y H^*,                  W=U H U^* H^*.
```

If `U` commutes with `X,Y,C`, then the exact arithmetic identity

```text
H = X Z X C                                             (RSC1)
```

implies the **self-commutator identity**

```text
W = X [W,Z] X^*.                                        (RSC2)
```

There is a robust dimension-free form.  If

```text
eta=||H-X Z X C||_2,
epsilon_X=||UX-XU||_2,
epsilon_Y=||UY-YU||_2,
epsilon_C=||UC-CU||_2,
```

then

```text
||W-X[W,Z]X^*||_2
 <= 2 eta+2 epsilon_X+epsilon_Y+epsilon_C.              (RSC3)
```

Consequently, for normalized trace and

```text
e_h=1-|tr(W)|^2,
```

one has

```text
||W-I||_2
 <= 2 sqrt(2 e_h)
    +2 eta+2 epsilon_X+epsilon_Y+epsilon_C.             (RSC4)
```

All constants are independent of matrix dimension.  For a fixed finite
presentation of `A`, `(RSC1)` has fixed area.  Moreover `X,Y,C` are fixed
words in `Lambda`.  Combining their word telescoping with the quantitative
perfectness estimate `(PTS4)` gives a presentation-dependent constant `K`
such that every approximate assignment satisfies

```text
||[U,rho(h)]-I||_2
 <= 2 sqrt(2 e_h)
    +K (sqrt(q_Lambda)+delta),                          (RSC5)
```

where

```text
q_Lambda=sum_(s in S_Lambda)
  (1-|tr([U,rho(s)])|^2).
```

Thus the scalar phase at the **target** is not part of the remaining SL3
wall: projective transfer immediately upgrades to ordinary commutator
transfer with a dimension-free modulus.  The unresolved direction remains
exactly the hard one, proving `e_h->0` from lattice energy and presentation
defect.  In particular `(RSC5)` is progress on the shape of the terminal,
not a proof of `projective-trace-square-transfer-for-sl3-pair`.

The identity cannot be run backwards from its immediate overlap-power
consequences.  The actual root elements also give `[W,Z^4]=[W,X^2]=1`, but
`sl3-self-commutator-overlap-packet-has-s3-leak` realizes these two
centralities and `(RSC2)` exactly in the regular representation of `S_3`
with `tr(W)=0`.  Hence a direct trace-square proof must retain further
same-microstate arithmetic coupling; the bounded self-commutator packet by
itself has a maximal finite-dimensional leak.
