---
rg: 2
id: normalizing-subgroups-double-coset-proof
kind: route
title: Put the difference of two double-coset representatives in the trivial intersection
target: normalizing-subgroups-separate-double-cosets
requires: []
artifacts:
  - research/artifacts/boone-higman-lean-preflight-2026-09-08.md
---

Suppose x,y lie in K and HxH=HyH. Choose a,b in H with y=a*x*b.
Normalization gives x*b*x^-1 in H, hence

    y*x^-1 = a*(x*b*x^-1) in H.

It also belongs to K. The trivial intersection makes y*x^-1=1,
so x=y. This proves injectivity and its infinite-bi-index consequence.

For the negative control, take a=(12), x=(123), y=x^-1 in S3,
H=<a>, K=<x>. Then H intersect K={1}, but y=a*x*a differs from x.
Here K does not normalize H.

The injectivity implication has a successful Lean replay in workflow
run 34282924692 at commit 2eb1b4670cdf49735546c3402d2d1d8e2de3db5b.
The exact CPU witness separately verifies the false control. No neural
generation was used in either proof or in this replay.
