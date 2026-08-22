---
rg: 2
id: sparse-anchor-odd-fourth-moment-is-the-renormalization-gate
kind: claim
title: Sparse anchor-odd fourth moments are the remaining random-anchor renormalization gate
distinct_from:
  balanced-overlay-diffuse-square-function-newton: that asks for a full row-column Newton inverse; this isolates the concrete sparse nonlinear estimate left after the one-anchor linear and quadratic terms are separated.
  dense-complete-pair-remainders-are-cb-quadratic: that controls the complete double average by a CP row factorization; this explains why the same argument loses length on bounded-degree face edges.
  all-dual-unique-neighbors-contract-operator-tails: that contracts scalar coordinate tails using parity geometry; this asks for the operator-valued two-odd-factor analogue on the low diffuse block.
---

OPEN.  For a uniformly random anchor `a`, put

```text
 Y_(a,i)=(Q_i-Q_a Q_i Q_a)/2.                           (SAF1)
```

After `one-anchor-grading-makes-parity-damage-quadratic`, the sparse
bounded-width parity remainder is controlled by terms

```text
 tau(Y_(a,i)^2 Y_(a,j)^2)                               (SAF2)
```

for pairs `(i,j)` co-occurring in a face (up to cyclic ordering and
contraction factors).  The needed dimension-free estimate is a bound of
the schematic form

```text
 E_a E_face sum_(i<j in face)
   tau(Y_(a,i)^2Y_(a,j)^2)
 <= o_b(1) E_a E_i tau(Y_(a,i)^2),                      (SAF3)
```

on the common low square-function block `H<=b`, with `o_b(1)->0`
independently of the code length.  Together with the exact-base random
anchor gap, `(SAF3)` would make the parity/sign terms a genuinely
quadratic perturbation and yield a strict expected contraction for small
`b`.

## Attempts

The dense complete-pair estimate does not imply `(SAF3)` for the sparse
face graph.  For a fixed anchor let `K_a=sum_iY_(a,i)^2`.  Summing over all
ordered pairs gives `tau(K_a^2)`, but the sparse face average has only
`Theta(L)` pairs rather than `Theta(L^2)`.  Comparing it to the dense
average therefore loses a factor `L`.

Bounded face degree alone gives

```text
 sum_((i,j) in E_face) tau(Y_(a,i)^2Y_(a,j)^2)
 <=D sum_i tau(Y_(a,i)^4),                              (SAF4)
```

using tracial Cauchy--Schwarz/Young.  A bound on the **average** positive
square function does not bound each `||Y_(a,i)||_infty`; consequently
`(SAF4)` is only linear in the Hilbert energy in the worst case.  This is
the sparse high-operator-norm loss already visible in the Newton audit.

The all-dual unique-neighbor recurrence is the natural extra input, but its
current form controls scalar tails of
`q_i^2=E_j||[Q_i,Q_j]||_2^2`, not the operator-valued fourth moment in
`(SAF2)`.  The next attack is therefore an operator unique-neighbor or
noncommutative stopping-time inequality which assigns every large product
`Y_(a,i)Y_(a,j)` to a charged parity residual without choosing different
physical cuts for different anchors.  Assuming individual operator bounds
on all `Y_(a,i)` would prove `(SAF3)` immediately, but is strictly stronger
than the common averaged square-function cut and cannot be inserted as a
hypothesis.
