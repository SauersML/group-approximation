---
rg: 2
id: finite-trace-profile-net-is-dimension-free-proof
kind: route
title: Compact cube proof of the finite trace-profile theorem
target: finite-trace-profile-net-is-dimension-free
requires: []
artifacts:
  - research/artifacts/nonhyperlinear-finite-moment-sparsification-2026-08-18.md
---

Every normalized trace of a unitary word lies in the closed unit disk, so its
real part lies in `[-1,1]`; therefore every `W`-profile lies in the fixed compact
cube `[-1,1]^W`.  The closure over the union of all matrix dimensions is a
closed subset of that compact cube and hence compact.  Subdivide each interval
`[-1,1]` into mesh at most `eta`; choosing one occupied point from every
occupied cube gives the stated dimension-free net bound.

The two normalized-HS identities are direct expansions of
`tr_n((A-B)^*(A-B))` using unitarity and traciality.  They show that relator
defect and pairwise short-word separation factor through the finite profile.
Finally `tr_{nm}(X tensor I_m)=tr_n(X)`, so amplification creates no new
profile coordinate.  This proves every clause of the claim.
