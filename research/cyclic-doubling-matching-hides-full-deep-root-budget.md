---
rg: 2
id: cyclic-doubling-matching-hides-full-deep-root-budget
kind: claim
title: Cyclic doubling covariance can be exponentially accurate while deep root mass tends to one
distinct_from:
  finite-dyadic-square-function-detects-deep-root-mass: that detects deep mass internally from dyadic power words; this proves that one root-scaling edge cannot charge that mass with a depth-independent coefficient.
  periodic-conductor-plateaux-pay-a-shared-root-seam: that constructs growing shift clocks and locates a constant defect at an adjacent-root seam; this gives the exact optimal one-edge spectral matching cost and directly compares it with the deep-mass projection.
  regular-dyadic-windows-have-unlimited-conjugate-mackey-capacity: that rules out projective multiplicity-capacity bounds on growing regular congruence windows; this is an elementary cyclic spectral counterpacket with no Mackey cocycle.
---

For `N>=2`, put `m=2^N`, `zeta=exp(2 pi i/m)`, and

```text
P_N=diag(1,zeta,zeta^2,...,zeta^(m-1)).                 (CDM1)
```

There is a permutation unitary `V_N` such that

```text
||V_N P_N V_N^*-P_N^2||_2^2
 =2 sin^2(pi/2^N),                                     (CDM2)
```

and this is the minimum over all permutation unitaries. On the other hand,
the deep projection of
`finite-dyadic-square-function-detects-deep-root-mass` has

```text
tr(D_>1)=1-2/2^N.                                      (CDM3)
```

Consequently no constant `C` independent of conductor depth can satisfy

```text
tr(D_>1)<=C inf_V ||V P_N V^*-P_N^2||_2^2.             (CDM4)
```

This is the smallest exact counterpacket to a one-edge deep-conductor
square-function estimate. It leaves no presentation or asymptotic issue:
the clock has exact `2^N` torsion, and the matching is an exact finite
permutation. The failure is spectral multiplicity transport. Therefore the
deep budget exposed after the bottom-A2 transfer cannot be paid by one
dyadic scaling edge, even with optimal finite-dimensional matching. A proof
must compare several root directions on one literal shared reservoir; the
constant seam in the six-chamber packet is indispensable.

