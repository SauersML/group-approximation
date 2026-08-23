---
rg: 2
id: one-julia-root-anchor-has-ideal-kernel-escape
kind: claim
title: One nontrivial Julia root anchor still has a proper-ideal kernel escape
artifacts:
  - research/artifacts/s3-mixed-root-julia-ideal-audit-2026-08-23.md
distinct_from:
  s3-packed-root-has-retractive-finite-escape: that kills the entire commutator root line; this retains and authentically Julia-anchors the unit root while killing only the designated coefficient coordinate.
  cyclic-acceptance-root-needs-kernel-reflection: that separates an uncoupled root packet from a positive acceptance coefficient; this tests the first non-retractive root/Julia coupling and locates its proper coefficient-ideal kernel.
  fixed-packet-julia-calculus-is-tracially-functorial: that gives the regular-tracial firewall for Julia functional calculus; this supplies an exact order-250 finite countermodel before any regular-factor argument.
---

**ESTABLISHED.**  A nontrivial Julia anchor on the coefficient unit does not
authenticate a designated packed coefficient.

Let `A=F_5[eps]/(eps^2)`.  The unital reduction `eps->0` induces

```text
UT_3(A) -> UT_3(F_5),
x_13(1) -> x_13(1)!=1,
x_13(eps) -> 1.                                      (JIK1)
```

The surviving unit root can be tied non-retractively to a literal Julia
commutator.  There are involutions `z,j` in the order-250 finite group

```text
K=UT_3(F_5) rtimes C_2
```

such that

```text
z j z j=x_13(1)!=1.                                  (JIK2)
```

The `C_2` actor swaps the two input root lines and inverts the commutator
root.  Hence all root additivity, every positive-root multiplication
triangle, the actor covariance, and `(JIK2)` hold exactly.  In the regular
representation the Julia off-diagonal block has normalized mass `1/4`.
Thus `(JIK2)` genuinely rules out the center-killing quotient used in
`s3-packed-root-has-retractive-finite-escape`.

It does not rule out `(JIK1)`.  Tensoring the exact scalar `S3` endpoint
payload gives

```text
F_00=F_01=F_11=0,
[Q,Z_X]=[Q,Z_Y]=0,
sum_(b,j)||D_(b,j)||_2^2=8,                           (JIK3)
```

while the designated root `x_13(eps)` has zero defect.  Therefore anchoring
`x_13(1)` does not imply one-coordinate kernel reflection for the packed
row.

The direct repair also fails at the stated level.  If the coupling is

```text
z j z j=x_13(eps),                                   (JIK4)
```

then after reduction the exact choice `j=z` satisfies `(JIK4)` with zero
Julia off-diagonal block, independently of the endpoint row.  Consequently
a direct Julia equality must additionally authenticate that off-diagonal
block as the representation-specific packed coefficient; the group word
equality alone does not do so.

The surviving mixed relation must therefore exclude proper coefficient
ideals containing `R` but not `1`, or enforce a same-reservoir correlation
between the Julia/Hecke block and the concrete endpoint row.  A unit anchor,
root multiplication table, actor covariance, and direct Julia word equality
do not supply that correlation.

