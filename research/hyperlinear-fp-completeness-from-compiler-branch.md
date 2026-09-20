---
rg: 2
id: hyperlinear-fp-completeness-from-compiler-branch
kind: route
title: Seed the MF-safe compiler with a finitely presented non-hyperlinear cover and use hyperlinearity of its positive branch
target: hyperlinear-fp-recognition-complete-iff-nonhyperlinear-group
requires:
  - mf-compiler-positive-branch-is-hyperlinear
  - mf-compiler-is-uniform-in-finite-seeds
  - local-approximation-properties-are-marked-closed
  - nonhyperlinear-presentation-codes-have-a-sigma2-upper-bound
---

## Why sufficient

If every group is hyperlinear, (A) holds.  Otherwise clause 4 of
[[local-approximation-properties-are-marked-closed]] gives a finitely
presented non-hyperlinear `E`.  The compiler of
[[mf-compiler-is-uniform-in-finite-seeds]] takes a finite presentation
code d for E and produces P_e(d). On FIN its group contains E, hence
is nonhyperlinear by heredity. On INF it is the actual R_e(d), whose
hyperlinearity follows from the seed-uniform positive hypothesis
[[mf-compiler-positive-branch-is-hyperlinear]].  Thus `INF <=_m HYP_fp`.
With the `Pi^0_2` upper bound this is (B).
