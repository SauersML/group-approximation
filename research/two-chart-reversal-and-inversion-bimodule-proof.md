---
rg: 2
id: two-chart-reversal-and-inversion-bimodule-proof
kind: route
title: Reverse the Toeplitz chain while swapping the left and right qutrit regular actions
target: raw-st-reversal-router-has-a-qutrit-bimodule-absorber
requires:
  - raw-root-hecke-gap-is-blind-to-qutrit-one-over-eighteen-cokernel
  - rectangular-commutant-and-qutrit-bimodule-absorber-proof
---

## The raw-root reversal

Use the convention

```text
S_N e_j=e_(j+1) for j<N-1,       S_N e_(N-1)=0,
T_N e_0=0,                       T_N e_j=e_(j-1) for j>0.
```

For `R_N e_j=e_(N-1-j)`, direct substitution gives

```text
R_NS_NR_N=T_N,                 R_NT_NR_N=S_N.             (TCB1)
```

The matrix `r_N=I_28 tensor R_N` commutes with every
`k tensor I_N` in the constant core. Conjugating a raw root by it and
using `(TCB1)` proves `(STR1)`. Also `r_N^2=1`, so
`theta_N` is an involutive inner automorphism of `F_N`.

## The qutrit left-right swap

Let `K=ell^2(F_0)`. On the group basis define

```text
L(u) delta_x=delta_(ux),
R(u) delta_x=delta_(x u^(-1)),
U delta_x=delta_(x^(-1)).                                (TCB2)
```

Both `L` and `R` are unitary representations, they commute, and

```text
U L(u)U=R(u),                    U R(u)U=L(u).             (TCB3)
```

Extend them linearly to `C[F_0]`. For the projection
`q_b=Ee_b`, put

```text
P_0=R(q_b),                       P_1=L(q_b).              (TCB4)
```

They are orthogonal projections of rank sixteen. Equation `(TCB3)`
gives

```text
UP_0U=P_1.                                                (TCB5)
```

## The two rectangular charts

Take two copies of `V tensor K` as target spaces and set

```text
Pi_0(g,u)=beta(g) tensor L(u),
Pi_1(g,u)=beta(g) tensor R(u),

Q_0=I_V tensor P_0,                 Q_1=I_V tensor P_1.   (TCB6)
```

The left-right commutation in `(TCB2)` says that `Q_epsilon`
commutes with `Pi_epsilon`. Hence

```text
H_(S,epsilon)=(I-Q_epsilon)H_(T,epsilon)
```

is invariant. Let `S_epsilon` be its inclusion and
`T_epsilon=S_epsilon^*`. Then

```text
T_epsilon S_epsilon=I,
S_epsilon T_epsilon=I-Q_epsilon,
Pi_epsilon(g,u)S_epsilon
  =S_epsilon Pi_(S,epsilon)(g,u).                         (TCB7)
```

Both heads have normalized target trace

```text
rank(Q_epsilon)/dim(H_(T,epsilon))
 =16/288
 =1/18.                                                   (TCB8)
```

Define the target router

```text
W_T=beta(r_N) tensor U.
```

It is an involution. Equations `(TCB1)`, `(TCB3)`, and `(TCB5)`
give

```text
W_T Pi_0(g,u)W_T=Pi_1(theta_N(g),u),
W_TQ_0W_T=Q_1.                                           (TCB9)
```

The second equation maps the complement of `Q_0` onto the complement
of `Q_1`. Its restriction is a unitary
`W_S:H_(S,0)->H_(S,1)`. Since the `S_epsilon` are literal
inclusions,

```text
W_T S_0=S_1 W_S,                                         (TCB10)
```

which completes `(STR2)`. In particular the router authenticates the
whole rectangular square.

## One finite unitary image

On each `H_(T,epsilon) direct-sum H_(S,epsilon)`, define

```text
z_epsilon=diag(I,-I),
a_epsilon=[ Q_epsilon  S_epsilon ].
              [ T_epsilon  0         ]
```

The inclusion equations give

```text
a_epsilon^2=z_epsilon^2=I,
(a_epsilon z_epsilon)^4=I.                               (TCB11)
```

Thus each pair generates a quotient of `D_8`. It commutes with its
chart carrier because `Q_epsilon` is in the commutant and
`S_epsilon` intertwines. Extend `W_T,W_S` to the direct sum of the
two chart pairs. Equations `(TCB9)--(TCB10)` show that it exchanges the
two carrier factors, the two actors, and the two gradings. Therefore the
full generated matrix group is a quotient of the finite semidirect product
in `(STR3)`.

Finally the finite shifts have two boundary projections:

```text
I-S_NT_N=E_(0,0),
I-T_NS_N=E_(N-1,N-1),
R_N(I-S_NT_N)R_N=I-T_NS_N.                               (TCB12)
```

They have identical normalized Hilbert--Schmidt size and are exchanged by
the exact router. The infinite Jacobson relation `TS=1` deletes the
second boundary while retaining `Q=1-ST`. Hence any law whose finite
decoding uses only `(TCB1)` and packet covariance is absorbed by this
model. The required next occurrence must couple one named endpoint
projection to the same qutrit chart after a return which is not invariant
under `R_N`.
