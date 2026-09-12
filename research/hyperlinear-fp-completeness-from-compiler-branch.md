---
rg: 2
id: hyperlinear-fp-completeness-from-compiler-branch
kind: route
title: Seed the MF-safe compiler with a finitely presented non-hyperlinear cover and use hyperlinearity of its positive branch
target: hyperlinear-fp-recognition-complete-iff-nonhyperlinear-group
requires:
  - mf-compiler-positive-branch-is-hyperlinear
  - mf-safe-finite-presentation-compiler
  - local-approximation-properties-are-marked-closed
  - nonhyperlinear-presentation-codes-have-a-sigma2-upper-bound
---

## Why sufficient

If every group is hyperlinear, (A) holds.  Otherwise clause 4 of
[[local-approximation-properties-are-marked-closed]] gives a finitely
presented non-hyperlinear `E`.  The compiler of
[[mf-safe-finite-presentation-compiler]] is uniform in its finitely
presented seed (its negative branch only embeds the seed through the
bridge and the Higman rope; its positive branch does not depend on the
seed's isomorphism type beyond finite presentability), so with seed `E`
it outputs `e |-> P_e` with `E <= Carrier(P_e)` for `e in FIN`, hence
non-hyperlinear by heredity, and `Carrier(P_e)` equal to the positive
branch for `e in INF`, hyperlinear by
[[mf-compiler-positive-branch-is-hyperlinear]].  Thus `INF <=_m HYP_fp`.
With the `Pi^0_2` upper bound this is (B).
