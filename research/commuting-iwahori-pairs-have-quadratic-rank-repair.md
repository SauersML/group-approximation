---
rg: 2
id: commuting-iwahori-pairs-have-quadratic-rank-repair
kind: claim
title: Jointly commuting Iwahori pairs have an explicit quadratic-rank repair although their smooth defect gradient vanishes
distinct_from:
  modular-multiplicities-reconcile-at-quadratic-rank-cost: that reconciles multiplicities with a supplied endpoint; this constructs a compatible endpoint from the defect when all four input generators commute jointly.
  iwahori-spectral-residual-gate-has-polynomial-step: that contracts under a low-singular-residual hypothesis; here every nonzero residual lies entirely in the adjoint kernel, and a discrete spectral repair replaces that step.
  strict-iwahori-repair-has-no-uniform-hs-neighborhood: that excludes a strict local modulus for general inputs; the jointly commuting subclass here has a strict linear bound and an explicit stationary sequence in compatible multiplicity strata.
artifacts:
  - research/artifacts/commuting-iwahori-repair-and-stationary-points-2026-09-08.md
---

Let `q=(S_1,B_1,S_2,B_2)` be an exact modular vertex pair on `C^n`.
Assume all four generator matrices commute with one another. For the
three fixed Iwahori word differences `R_j`, use

```text
e^2=sum_(j=1)^3 ||R_j||_2^2,
g=2 sin(pi/12).
```

There is an explicitly selected common reducing projection `P` with

```text
rank(P)/n <= e^2/g^2.
```

Replacing all four generators by the identity on `P`, while keeping
their action on its orthogonal complement, gives an exact compatible
pair in the same dimension. Its generatorwise rank distance is at
most `rank(P)` and its maximum normalized-HS distance is at most
`2e/g`. No compatible endpoint is supplied as input.

In the natural exact modular charts, however, `L* f=0`, where
`f=(R_j)`, `L` is the residual derivative, and `L*` is its real HS
adjoint. If `e>0`, the entire residual belongs to `ker(LL*)`, so
the low-singular-residual hypothesis of the polynomial step fails
maximally. Every update `L* p(LL*) f` is zero for every polynomial `p`.

There are explicit such noncompatible stationary pairs with
`e=sqrt(24/n)` and supplied compatible points in the same torsion
multiplicity stratum at distance at most `2sqrt(12/n)`. Thus even
same-stratum HS proximity does not make the spectral hypothesis
automatic. These examples have the explicit strict repair above;
they do not obstruct flexible stability or methods that perform
discrete surgery, select other directions, or use second derivatives.
