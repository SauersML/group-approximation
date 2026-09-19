---
rg: 2
id: expanding-finite-projective-branching-modules-vanish
kind: claim
title: Expanding finite projective branching modules over norm matrix coronas vanish
root: true
artifacts:
  - research/expanding-finite-projective-branching-modules-vanish-proof.md
distinct_from:
  corona-projective-hilbert-hotel-cancellation: that is the one-state self-duplication theorem; this treats an arbitrary finite recurrent system of mutually dependent projective modules.
  perron-frobenius-branching-carrier-collapse: that is a quantitative tracial leakage inequality; this is an exact module theorem in every norm matrix corona, including projections with arbitrarily sparse coordinate support.
---

Let `Q_d` be a norm matrix corona, let `A=(a_ij)` be a finite nonnegative
integer matrix, and let `P_1,...,P_N` be finitely generated projective right
`Q_d`-modules satisfying

```text
P_i ~= directSum_(j=1)^N P_j^(directSum a_ij)            (EPM1)
```

for every `i`.

If `A` admits a positive rational pressure vector

```text
A^T y >= (1+kappa)y,
y in Q_(>0)^N,  kappa in Q_(>0),                         (EPM2)
```

then

```text
P_1=...=P_N=0.                                           (EPM3)
```

In particular, `(EPM3)` holds for every strongly connected finite branching
system having at least one genuine branch.  The binary Hilbert-hotel equation
`P~=P directSum P` is the one-state matrix `A=[2]`.

Define the universal finite branching algebra `L_A` by orthogonal vertex
idempotents `v_i` and branch generators which implement `(EPM1)`.  Any
unital action

```text
L_A -> End_(Q_d)(P)                                      (EPM4)
```

on a finitely generated projective module decomposes `P` into the vertex
modules `P_i=v_iP`.  If `(EPM2)` holds, all vertex modules vanish, so `P=0`.
Consequently an expanding finite branching algebra has no nonzero unital
finite-projective realization over any norm matrix corona.

More generally, every closed irreducible component of `A` which is
supercritical has zero module at each of its vertices.  Substitution of
branching systems is multiplicative: an `A`-decomposition followed by a
`D`-decomposition yields an `AD`-decomposition.  This provides a finite
composition calculus for detecting impossible projective-module actions.
