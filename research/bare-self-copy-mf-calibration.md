---
rg: 2
id: bare-self-copy-mf-calibration
kind: claim
title: Exact finite-dimensional self-copy sterility does not imply MF sterility
distinct_from:
  compression-defect-dies-in-finite-dimensions: That theorem proves exact finite-dimensional sterility for every compression-centralizer defect; this gives one torsion-free finitely presented operator-MF group in which such a nontrivial defect survives in a norm corona.
  infinite-cyclic-compression-lamp-mf: That countermodel uses an infinite lamp orbit over a residually finite compressor; this is the three-generator one-relator-plus-commutator calibration with literal parent and child C-star algebras equal at every matrix stage.
artifacts:
  - notes/FINITE_PACKET_SELF_COPY_COLLAPSE.md
  - GroupApproximation/Criterion/FiniteDimensionalKill.lean
  - GroupApproximation/Algebra/DyadicRationals.lean
  - experiments/verify_bs12_calibration.py
---

Let

```text
G = <a,t,p | t a t^-1 = a^2, [p,a^2] = 1>,    w=[p,a].
```

Then `G` is torsion-free and finitely presented, `w != 1`, every honest
finite-dimensional linear representation kills `w`, but `G` is operator-MF
and a norm-matrix-corona representation keeps `w` nontrivial.

Algebraically,

```text
G = BS(1,2) *_<a²> Z².
```

The word `p a p^-1 a^-1` is reduced in the amalgam, while both factors are
torsion-free and amenable.  Shulman's amenable-amalgam theorem therefore makes
the full group C-star algebra MF.  Exact finite-dimensional invisibility is
the one-step specialization of `compression-defect-dies-in-finite-dimensions`.

There is also a direct matrix escape.  On `C^(2m)` the parent clock `A_m`, its
permuted conjugate `B_m`, and the two-fiber swap `P_m` satisfy

```text
||B_m-A_m^2|| -> 0,    [P_m,A_m^2]=1,
||[P_m,B_m]-1|| -> 0,  [P_m,A_m]=-1.
```

Moreover `C*(A_m)=C*(B_m)` is the full diagonal algebra.  Thus even exact
parent/child algebra equality does not provide the missing dimension-free
commutant coercivity.  The calibration refutes the bare inference

```text
exact finite-dimensional self-copy sterility => MF-radical membership.
```
