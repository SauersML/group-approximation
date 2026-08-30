---
rg: 2
id: stw99-xciv-some-tuple-avoids-all-exact-cores
kind: claim
title: Some finite tuple in the hyperfinite factor stays uniformly far from every exact core
distinct_from:
  stw99-xciv-some-finite-tuple-has-positive-fd-radius: that theorem separates one tuple from finite-dimensional subalgebras; this theorem separates one tuple from every exact subalgebra, including infinite-dimensional nuclear and Jiang--Su-stable exact cores.
  stw99-xciv-zstable-core-radius-controls-block-defect: that theorem gives a positive estimate using arbitrary Z-stable cores; this theorem proves that exact Z-stable cores cannot approximate every finite tuple and forces any universal core construction to use nonexact hulls.
  stw99-xciv-commutant-capacious-radius-controls-block-defect: that estimate permits nonexact tensor cores and is not obstructed by this theorem; the present result concerns exactness rather than relative-commutant size.
  stw99-problem-x2-hyperfinite-factor-quasidiagonal: that root asks for quasidiagonality of R; this finite local exactness obstruction neither proves nor refutes quasidiagonality.
artifacts:
  - research/artifacts/stw99-xciv-exact-core-barrier-audit-2026-08-30.md
---

There are a finite set `F subset R` and a constant `c>0` such that

```text
inf_A max_(x in F) dist(x,A) >= c,
```

where the infimum is over all unital exact C-star subalgebras `A subset R`.
Consequently this one tuple cannot be approximated in operator norm by
nuclear, AF, ASH, finite-nuclear-dimension, or exact `Z`-stable cores.

Indeed, if every finite tuple had distance zero from some exact subalgebra,
then every finite-dimensional operator subspace of `R` could be perturbed,
with arbitrarily small completely bounded distortion, into an exact
subalgebra.  Kirchberg's local operator-space characterization of exactness
would make `R` exact.  But orthogonal corners in `R` give a unital copy of
the nonexact algebra `product_(n>=1) M_n`, and exactness passes to
C-star subalgebras.  This contradiction also gives the uniform positive
constant `c` by negating the local approximation statement.

This is a genuine barrier to a nuclear-core proof of Problem XCIV, not a
negative solution of XCIV.  Jiang--Su stability by itself does not imply
exactness.  If XCIV has a positive answer, then any separable `Z`-stable
subalgebra of `R` containing this hard tuple must be nonexact.

