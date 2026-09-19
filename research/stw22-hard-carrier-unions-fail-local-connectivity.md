---
rg: 2
id: stw22-hard-carrier-unions-fail-local-connectivity
kind: claim
title: Multiplicity-three unions of hard carrier branches are not uniformly locally connected
distinct_from:
  stw22-diffuse-stiefel-uniform-loop-fillings: that theorem successfully patches hard carriers over a circle by an ordered cyclic interpolation; the present theorem shows why direct higher-dimensional union selection fails.
  stw22-fixed-factor-weighted-copy-uniform-s2-fillings: that positive theorem uses a pointed contraction of one fixed ambient factor and does not select hard carriers over S2.
artifacts:
  - research/artifacts/stw22-s2-hard-carrier-obstruction-audit-2026-08-30.md
---

Let `N` be a `II_1` factor.  There are norm-continuous pairs of equal-trace
carrier projections `p_1(theta),p_2(theta)` and a fixed target trace `s`
such that the branch union

```text
Phi(theta)
 ={E in Proj(N):tau(E)=s, E>=p_1(theta)}
  union
  {E in Proj(N):tau(E)=s, E>=p_2(theta)}
```

is not an equi-locally-path-connected family at `theta=0`.  For every
`delta>0`, some `theta>0` admits `E_theta,F_theta in Phi(theta)` with
`||E_theta-F_theta||_2<delta`, while every path between them inside
`Phi(theta)` leaves a fixed positive-radius ball.

Moreover, adjoining a simplex coordinate does not make the corresponding
intersection-valued multifunction lower semicontinuous.  If positive
barycentric coordinates require the selected projection to contain both
active carriers, a pair which coincides at `theta=0` and splits at
`theta>0` forces a fixed-trace transverse projection to appear abruptly.

Thus the naive multiplicity-three Michael-selection bootstrap for an
`S^2` spectral carrier is invalid.  This does not disprove a
two-dimensional spectral-capture theorem; it proves that any valid proof
must soften the containment relation or synchronize the local carriers
before applying selection.
