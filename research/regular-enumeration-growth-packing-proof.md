---
rg: 2
id: regular-enumeration-growth-packing-proof
kind: route
title: Pack a word ball into the interval reachable by its enumerated generator steps
target: regular-enumeration-displacement-bounds-growth
requires: []
artifacts:
  - research/artifacts/boone-higman-finite-ray-compiler-boundary-2026-09-08.md
---

For p in B_r, write p=s_l ... s_1 with l<=r, and follow the path
1,s_1,s_2*s_1,...,p. Before each generator step the current vertex lies
in B_(r-1), so each change of nu is bounded by D_nu(r). Therefore

    |nu(p)-nu(1)| <= r*D_nu(r).

Injectivity packs B_r into an integer interval of length 2r*D_nu(r),
which contains 2r*D_nu(r)+1 integers. This proves the inequality.
If all generator displacements are bounded by C, the same inequality
gives |B_r|<=2Cr+1 for every r.

For Z^2 with the standard symmetric generators, the radius-k sphere
has 4k points for k>=1. Hence

    |B_r|=1+sum_(k=1)^r 4k=1+2r(r+1).

Substitution and division by 2r give D_nu(r)>=r+1.

No classification theorem about groups of linear growth is needed for
this inequality or the Z^2 consequence.

