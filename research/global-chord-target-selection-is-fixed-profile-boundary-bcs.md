---
rg: 2
id: global-chord-target-selection-is-fixed-profile-boundary-bcs
kind: claim
title: Global chord target selection is a fixed-profile boundary BCS, not merely a transport polytope
distinct_from:
  finite-chord-context-is-joint-table-plus-collision: that classifies one context after its target tuple is fixed; this identifies the simultaneous global target-choice problem left by that theorem.
  coherent-balanced-context-permutations-would-give-a-ce-trace: that treats permutation gauges and hence a globally diagonal model; this separates that integer transport sector from the general noncommuting matrix problem.
  finite-sheet-transport-networks-are-exactly-matricial: that retains edge covariance and arbitrary monodromy; this asks for literal equality of every shared variable and therefore removes the transport arrows.
---

**ESTABLISHED REDUCTION AND OBSTRUCTION.**  Let `X` be the variables of a
finite BCS, let `U_c` and `R_c subset {+1,-1}^{U_c}` be its contexts and
allowed assignments, and let `B_c subset U_c` be the variables of context
`c` which must be identified with another context.  Fix balanced integer
multiplicities

```text
n_(c,a)>=0,            sum_(a in R_c)n_(c,a)=D,
N_c(beta)=sum_(a|_(B_c)=beta)n_(c,a).                    (GTS1)
```

After a spanning-tree gauge, the global finite-matrix target-selection
problem left by `finite-chord-context-is-joint-table-plus-collision` is
exactly the following:

```text
find selfadjoint involutions Z_x in M_D(C), x shared,
[Z_x,Z_y]=0 whenever x,y in B_c,
rank(product_(x in B_c)(1+beta_x Z_x)/2)=N_c(beta)       (GTS2)
```

for every context `c` and boundary pattern `beta`.  In particular this is
the finite-dimensional representation problem for the **boundary-projected
BCS with the full context trace profile `(GTS1)` fixed**.  It is a compact
real-algebraic feasibility problem, but in general it is not a finite linear
transport problem: variables belonging to different contexts need not
commute.

If one additionally requires all `Z_x` to commute, `(GTS2)` is equivalent to
the integer multi-marginal transport system

```text
m_gamma in Z_>=0,
sum_(gamma|_(B_c)=beta)m_gamma=N_c(beta)                 (GTS3)
```

on global boundary assignments `gamma in {+1,-1}^X`.  Thus the usual
transport polytope describes precisely the diagonal/classical sector, not
the full target problem.

The rank-balanced atlas does **not** guarantee a solution of `(GTS2)`.
Already take three variables and the three two-variable contexts

```text
{1,2}, {2,3}, {3,1},
```

with every local assignment allowed and `D=2`.  Give the first two contexts
rank one on `++` and `--`, and the last rank one on `+-` and `-+`.  Every
one-variable `+/-` rank is `(1,1)`, so all incidence marginals are perfectly
balanced.  But `(GTS2)` would force

```text
Z_1=Z_2,       Z_2=Z_3,       Z_3=-Z_1,
```

which is impossible for an involution.  Hence full joint compatibility is a
strict global condition invisible to the balanced one-variable polytope.

If every context variable is shared, `B_c=U_c`, then any solution of
`(GTS2)` is an ordinary finite-dimensional representation of the original
BCS (with the prescribed context ranks), and conversely.  Therefore the
fixed no-Connes-embeddable BCS used by the signed-Hecke program has no such
finite-matrix global target.  When private variables remain, `(GTS2)` is the
finite-dimensional model of the existential boundary projection; residual
assignment collisions are exactly multiple allowed private extensions of
one boundary pattern.  The free-phase escape can exploit those fibers only
*after* `(GTS2)` has been solved; it does not solve its global obstruction.

