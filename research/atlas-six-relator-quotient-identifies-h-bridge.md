---
rg: 2
id: atlas-six-relator-quotient-identifies-h-bridge
kind: claim
title: The five saturated boundary rows and 19243 centrality identify the two rank-three chart subgroups
refuted_by: atlas-charts-overlap-trivially
distinct_from:
  atlas-a4-19243-parabolic-normal-closure: that computes the normal closure of one collision translation inside one chart; this concerns bridge elements between two chart factors.
  atlas-five-row-operator-phase-lift: that is the resulting normalized-HS inequality; this is its purely group-theoretic sufficient condition.
---

**REFUTED.**  The proposed target was the following.  Work in the coordinates obtained by transporting the second
`A8` chart through the certified classical alignment.  Let

```text
Gamma_6=(A8_1*A8_2)/<<s_0,s_11,s_30,s_44,s_55,c_19243>>,       (SXB1)
```

where the five `s_j` are the saturated first-boundary words and
`c_19243` is the transported interior commutator.  Both copies contain the
literally labelled subgroup

```text
H=diag(GL_3(F2),1) ~= GL_3(2).
```

Prove that the two maps from `H` to `Gamma_6` agree.  Equivalently, for the
four standard transvections `T` generating `H`, prove

```text
i_2(t)i_1(t)^-1=1 in Gamma_6                 (t in T).          (SXB2)
```

This is a finite normal-closure problem.  Any proof supplies four finite van
Kampen expressions in conjugates of the six displayed relators; no uniform
family or asymptotic filling theorem is being requested.

It cannot hold.  Every `s_j` is a genuine word in the kernel of

```text
A8_1*A8_2 -> L_(F2)(1,2)^x,
```

and `atlas-19243-centrality-is-bar-s-consequence` puts `c_19243` in the
same kernel.  Hence the normal closure of the six relators is contained in
that true kernel.  By `atlas-charts-overlap-trivially`, both chart maps into
the Leavitt unit group are faithful and their images intersect trivially.
For every nonidentity `t in H`, therefore,

```text
i_2(t)i_1(t)^-1 != 1
```

already in the exact Leavitt quotient, and thus also in `Gamma_6`.  No bridge
in `(SXB2)` has a van Kampen filling by these six relators.

This is the exact reason the six-relator ordinary-group compression cannot
prove the phase lift.  The analytic claim concerns only finite regular-margin
representations; the universal quotient has an infinite exact representation
which retains the bridge.

## Exact finite audit

In the natural alternating overgroups, exact exhaustive evaluation gives

```text
ambient     conjugators     five-row survivors     plus-c survivors
A9             362880               1                     0
A10           3628800               2                     0.
```

The `A9` survivor is the diagonal labelled chart.  The two `A10` survivors
differ by the order-two pointwise-chart centralizer and define the same
second chart.  Thus neither overgroup supplies a six-relator solution.  A
GAP iterator evaluates the `A10` census in nine seconds on one MSI core by
rejecting on the first failed row.  These audits are finite evidence only and
do not prove `(SXB2)` in the universal quotient.

The next natural alternating degree is now also exhausted by
`atlas-six-relator-has-no-a11-target`.  Every nontrivial `A8 -> A11` map has
one natural eight-point orbit and three fixed points, so the complete labeled
pair census has `11!/3!=6,652,800` cases.  Exactly one case satisfies the five
boundary rows and it fails `c_19243`; hence there is no plus-centrality
survivor in `A11` either.

## Falsification criterion

A finite quotient `F` of `Gamma_6` in which both marked `A8` factors inject
and at least one bridge in `(SXB2)` survives refutes
`atlas-five-row-operator-phase-lift`.  Indeed, the left regular
representation of `F` restricts to `[F:A8]` copies of the regular
representation on either chart.  After a unitary identification of these two
restrictions, all six nonlinear defects vanish.  A surviving bridge gives
positive `H` covariance, and the established five-row linear coercivity then
forces at least one of the five linear energies to be positive.
