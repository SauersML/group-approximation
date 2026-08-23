---
rg: 2
id: raw-prefix-covariance-reduces-to-nonincidence-cap-commutators
kind: claim
title: Raw cap-prefix covariance reduces exactly to nonincidence commutators
artifacts:
  - experiments/or3_cycle_raw_prefix_covariance.py
distinct_from:
  sequential-overlap-polar-aligns-carriers-not-contexts: that extracts and polar-corrects one positive sequential profile but leaves SPA12 as an undifferentiated raw covariance estimate; this gives the exact telescope, handles the source cut by a common coarea threshold, and isolates the rows which still need word payment.
  full-support-factor-refutes-exact-exhaustive-typed-cap-chain: that proves exact universal typed rows are incompatible with the full-support witness; this gives a positive dimension-free reduction for canonical matrix tuples and a smallest exact OR3-cycle witness showing why incidence rows alone cannot suffice.
---

**ESTABLISHED.**  Let `q_1,...,q_m` be projections in a finite tracial
matrix algebra, let

```text
X=q_m...q_1,             H=X^*X,                       (RPC1)
```

and suppose `tau(H)>=a>0`.  Let `B_x` be a fixed finite family of
self-adjoint unitaries.  For a context occurrence `(c,x)`, let `A_(c,x)` be
a self-adjoint unitary commuting with `q_c`, and put

```text
r_(c,x)=A_(c,x)q_c-q_cB_x.                             (RPC2)
```

For every projection `P` and `Y_c=q_c...q_1P`, direct multiplication gives
the exact identity

```text
A_(c,x)Y_c-Y_cB_x
 =r_(c,x)q_(c-1)...q_1P
  +q_c sum_(j<c) q_(c-1)...q_(j+1)[B_x,q_j]
                         q_(j-1)...q_1P
  +q_c...q_1[B_x,P].                                   (RPC3)
```

If `x` occurs in context `j`, then its incidence row already pays the
corresponding cap commutator:

```text
||[B_x,q_j]||_2<=2||r_(j,x)||_2.                       (RPC4)
```

Indeed `A_(j,x)` commutes with `q_j`, and subtracting `(RPC2)` from its
adjoint gives `[B_x,q_j]=r_(j,x)-r_(j,x)^*`.  Consequently the only middle
terms in `(RPC3)` not controlled by the ordinary incidence rows are those
for contexts `j` which do **not** contain `x`.

The source projection can be chosen without creating an additional
authentication problem.  There is one common threshold

```text
t in [a/4,a/2],          P=1_[t,1](H),                 (RPC5)
```

for which

```text
tau(P)>=a/(2-a),          H>=tP,                       (RPC6)

sum_x ||[B_x,P]||_2^2
 <=(4/a) sum_x ||[B_x,H]||_2.                         (RPC7)
```

To prove `(RPC7)`, diagonalize `H`.  Spectral coarea and Cauchy--Schwarz
give

```text
int_0^1 ||[B_x,1_[t,1](H)]||_2^2 dt
 <=||[B_x,H]||_2.                                     (RPC8)
```

Sum over the fixed variable menu and average over the interval in `(RPC5)`.
Also

```text
||[B_x,H]||_2
 <=2 sum_j ||[B_x,q_j]||_2.                           (RPC9)
```

Thus, for a fixed finite instance, vanishing incidence-row energy together
with vanishing nonincidence cap-commutator energy implies the complete raw
prefix covariance `(SPA12)` with a dimension-independent vanishing modulus.
The cut still has the fixed source density and singular-value floor needed
by `polar-correction-preserves-povm-covariance`; using `a/4` instead of
`a/2` only changes its fixed constant.

## The nonincidence term is necessary in the smallest full-support model

Take three OR3 contexts in the Berge triangle

```text
c_1 -- x_12 -- c_2 -- x_23 -- c_3 -- x_31 -- c_1.     (RPC10)
```

There is an exact model in `M_7(C)` with a full-support rank-one PVM on all
seven satisfying OR3 assignments in every context and a rank-four Fano-cap
projection `q_c` in every context such that all six compressed incidence
rows in `(RPC2)` vanish.  Nevertheless, for the order `(c_1,c_2,c_3)`,

```text
tau(X^*X)=3/14,
spec(X^*X)={1,1/2,0,0,0,0,0},                         (RPC11)
P=1_[3/28,1](X^*X),
||A_(3,x_31)X P-X P B_(x_31)||_2^2=1/7.              (RPC12)
```

Every term of `(RPC3)` vanishes except

```text
q_3[B_(x_31),q_2]q_1P,                                (RPC13)
```

whose squared norm is exactly `1/7`.  The artifact constructs the three
PVMs and all matrices over the rational numbers and verifies every identity
without numerical tolerances.  Dimension seven is minimal because a
full-support OR3 PVM has seven nonzero pairwise orthogonal atoms.

Therefore `(SPA12)` cannot be obtained from occurrence-local coefficient
links, cap mass, and prefix telescoping alone.  The exact remaining payment
is cross-context: a transported variable must charge its passage through
the first cap belonging to a context which omits it.
