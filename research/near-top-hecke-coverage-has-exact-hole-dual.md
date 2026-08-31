---
rg: 2
id: near-top-hecke-coverage-has-exact-hole-dual
kind: claim
title: Near-top Hecke coverage has an exact small-trace hole dual
distinct_from:
  almost-full-hecke-frame-gives-flexible-corner: that turns one almost-full contractive frame into a quantitative finite corner; this computes the optimal trace coverage and its exact dual obstruction.
  regular-hecke-kraus-support-has-exact-order-dual: that dualizes the support function of the entire relative matrix range; this dualizes only the contractive coverage of a chosen near-top spectral subspace.
  hecke-top-spectrum-coverage-controls-window: that uses an exactly unital top or near-top frame; this allows a trace-small uncovered carrier and characterizes the best such carrier.
---

Use the regular finite-core notation

```text
D=(lambda_G(B))',
T_X(A)=E_D(X_0 A X),
Q_epsilon=1_[1-epsilon,1](T_X) on L^2(D,tau).
```

Define the optimal contractive coverage of the near-top space by

```text
c_epsilon=max tau(P),
P=sum_j A_j*A_j <= 1,       A_j in Q_epsilon L^2(D).   (HCD1)
```

Then `0<=c_epsilon<=1`, the maximum is attained, and it has the exact
finite SDP dual

```text
c_epsilon
 =min {tau(Z): Z in D, Z>=0,
       Q_epsilon R_Z Q_epsilon >= Q_epsilon},          (HCD2)
```

where `R_Z(A)=AZ` and the inequality acts on `L^2(D,tau)`. The feasible
choice `Z=1` shows directly that the dual value is at most one.

Combining (HCD1) with the almost-full-frame theorem gives the computable
upper bound

```text
Delta^reg_(G,B)(X)
 <= sqrt(2 epsilon + 4(1-c_epsilon)).                  (HCD3)
```

Thus a positive solution of the regular Iwahori finite-corner gate follows
from any moving choice

```text
epsilon_n -> 0,       c_(epsilon_n) -> 1.              (HCD4)
```

The contrapositive gives a sharp concrete signature for every possible
negative sequence. If

```text
Delta^reg_(G_n,B_n)(X_n) >= eta > 0
```

and `0<epsilon<=eta^2/4`, then there is an attained dual certificate
`Z_(n,epsilon)>=0` such that

```text
tau(Z_(n,epsilon)) <= 1-eta^2/8,
Q_epsilon R_(Z_(n,epsilon)) Q_epsilon >= Q_epsilon.    (HCD5)
```

Equivalently, every near-top Hecke vector obeys

```text
tau(Z A*A) >= ||A||_2^2.                               (HCD6)
```

So an actual obstruction cannot merely have a thin top eigenspace. It must
place the entire near-top spectral band under a right-multiplication
majorant whose normalized trace stays uniformly below one. Conversely,
ruling out the certificates (HCD5) as `epsilon->0` proves almost-full
coverage and produces the flexible finite corner.

This is the exact complete-order frontier left by the relative lifting
program. Ambient LLP, local reflexivity, MF, and the modular
Fejer--Riesz factorization do not estimate the minimum in (HCD2) over the
moving Iwahori commutants. The nonhyperlinear-group root remains open.

DERIVATION
near-top-hecke-coverage-hole-dual-proof
