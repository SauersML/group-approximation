---
rg: 2
id: fractional-source-branch-pressure
kind: claim
title: Branch pressure survives partial source coverage, and two children need only fractions summing above one
artifacts:
  - research/artifacts/fractional-branch-pressure-2026-08-19.md
distinct_from:
  perron-frobenius-branching-carrier-collapse: that requires every branch to have source exactly a whole state projection and an integer incidence matrix; this permits each branch to cover only a fraction of its state and produces a rational incidence matrix.
  rational-supercritical-branch-certificate: that is the pure linear-algebra certificate for a nonnegative integer matrix once the coordinate inequality is given; this supplies the coordinate inequality for fractional sources and shows the certificate step is unchanged over the rationals.
  gram-branching-capacity-with-overlap: that is the one-target capacity inequality; this assembles the per-target inequalities into a rational branch matrix and runs the pressure argument.
  strongly-connected-branching-gives-rational-pressure: that produces a subeigenvector from strong connectivity plus one integer branch; this concerns fractional coverage and its conclusion is a condition on fraction sums, not on connectivity.
---

Let `(M,tau)` be a finite tracial von Neumann algebra.  Fix projections
`P_1,...,P_m` with `x_i=tau(P_i)`, and a finite edge set where each edge
`e:i->j` carries a partial isometry `T_e` whose source projection

```text
E_e = T_e^* T_e
```

satisfies `E_e <= P_i` together with a *fractional coverage* bound

```text
tau(E_e) >= c_e x_i - a_e,          c_e >= 0 rational, a_e >= 0.   (FSB0)
```

Define the rational branch matrix, the per-target error, and the total error by

```text
B_(ji) = sum_(e: i->j) c_e,
l_j = sum_(e: ->j) ||(1-P_j)T_e||_2^2,
o_j = sum_(e != f, both ->j) ||T_e^* T_f||_2^2,
eta_j = sum_(e: ->j) a_e + 2 l_j + o_j.
```

Then, coordinatewise,

```text
x >= B x - eta.                                                     (FSB1)
```

If moreover there are a positive rational vector `y` and a rational `kappa>0`
with

```text
B^T y >= (1+kappa) y,                                               (FSB2)
```

then

```text
kappa (y . x) <= y . eta.                                           (FSB3)
```

**Two-child corollary.**  Let `P,R_0,R_1` be states, let the two edges
`P->R_0`, `P->R_1` have full coverage `c=1` (as the exact atlas Pauli cell
does), and let single return edges `R_i->P` have coverage `q_i`.  The branch
matrix on `{P,R_0,R_1}` has spectral radius `rho` with

```text
rho^2 = q_0 + q_1.
```

Hence the network is supercritical if and only if

```text
q_0 + q_1 > 1,                                                      (FSB4)
```

and a rational certificate `(y,kappa)` exists whenever `(FSB4)` holds with
rational `q_i`.  Neither child has to return almost completely, and no cycle of
single full-coverage returns is ever needed: a cycle whose edges all have
coverage at most one and no branching has spectral radius at most one, so
branching is the only source of pressure and fractional returns are the only
thing the search has to find.

## What this changes for the search

`atlas-pauli-range-packing-recurrence` and
`atlas-pauli-branch-recurrence-automaton` both require every edge's source to
be exactly the state projection `P_i`, i.e. an approximate containment
`w P_i w^* <= P_j`.  Under `(FSB0)` that requirement becomes a *quantity*
`c_e in (0,1]` rather than a hypothesis, and by
`soft-block-mass-yields-fractional-branch` the quantity is computed from an
ordinary block moment `||P_j w P_i||_2^2`.  The search target changes from "find
a return word" to "find a weighted network whose reproduction number exceeds
one", which is `atlas-fractional-pauli-return-network`.
