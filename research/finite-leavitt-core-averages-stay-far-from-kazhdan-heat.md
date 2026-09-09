---
rg: 2
id: finite-leavitt-core-averages-stay-far-from-kazhdan-heat
kind: claim
title: Every fixed finite Leavitt core average stays far from the native Kazhdan average
distinct_from:
  diagonal-leavitt-models-have-external-commutant-excess: That compares native left and right algebras in a tensor-diagonal embedding; this gives distance one between finite-core and full-left invariant projections in every canonical embedding.
  leavitt-finite-trace-tests-regularize-both-factor-profiles: That corrects finite-factor multiplicities; this tests whether regular finite cores can supply a uniform approximation of the full native averaging map.
artifacts:
  - research/artifacts/leavitt-finite-core-averaging-separation-2026-09-08.md
---

Let `H=GL_4(R)`, `R=L_(F_2)(1,2)`, and let `L=diag(EL_3(R),1)`.
Write `N=L(H)` with its canonical trace. The standard finite coefficient
cores give nested groups `F_d=GL_(3*2^d)(F_2)<=L`.

For every finite tracial extension `N<=Q`, put

```text
E_d=E_(L(F_d)' intersect Q),   E=E_(L(L)' intersect Q).
```

Then `||E_d-E||_(infinity->2)=1` for every `d`. If `T` is a fixed
lazy adjoint Kazhdan average for `L`, with gap `gamma>0`, then

```text
||E_d-T^j||_(infinity->2) >= 1-(1-gamma)^j.
```

For each `d` the lower bound is witnessed by one explicit nonidentity
tail unitary belonging to the represented group `L`. In a matrix tracial
ultraproduct, or in `R_hyp^omega`, there is also a single unitary commuting
with the entire increasing core `F_infinity` and having conditional
expectation zero onto the full-left commutant.

The artifact gives a finite word-trace version of the separation. It
does not identify ultraproducts of coordinate commutants for cores whose
depth varies with the coordinate. Such a moving-depth construction
needs its own estimates, including the displayed trace tests at that
depth. Neither nonhyperlinearity nor a uniform matrix-relator gap follows.
