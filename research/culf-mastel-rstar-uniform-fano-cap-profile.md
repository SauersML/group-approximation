---
rg: 2
id: culf-mastel-rstar-uniform-fano-cap-profile
kind: claim
title: Uniformly select a Fano-cap affine support branch for the Culf--Mastel R-star family
distinct_from:
  perfect-completeness-constant-soundness-lcs-compiler: that asks for any effective perfect-gap LCS compilation; this isolates the narrower one-ghost support-profile selector after local affine soundness is proved.
  bcs-to-lcs-exact-support-gap: that asks for one static exact robust sub-menu; this must work uniformly over the machine-indexed Culf--Mastel family and preserve its RE orientation.
---

OPEN.
Realize the Culf--Mastel perfect-gap family over the fixed non-Schaefer
relation `R_*`, and effectively output one finite marked LCS instance such
that:

```text
M halts     => some perfect CE R_* strategy is represented on a
               Fano-cap support profile and gives J != 1,
M nonhalts  => every marked approximate LCS model would restrict to a
               perfect CE R_* strategy.                              (UFC1)
```

For any **fixed** cap profile, the local affine replacement is sound by
`rstar-fano-cap-support-preserves-nonru-affine-relaxation`.  The missing
operation is an effective finite OR over the possible cap profiles (or a
presentation-level rule which canonically selects one).  Identifying all
branch central signs is an AND, not an OR: a single unsatisfiable branch can
kill the shared sign.  A direct sum of game algebras is likewise not an
ordinary solution-group construction with one authenticated central mark.

## Attempts

Pairwise pruning removes an atom with no compatible neighbor, and
`commuting-neighborhood-pruning-pays-atom-mass` removes an atom with no joint
extension when all neighbor PVM algebras commute.  General oracular 2-CSP
strategies do not provide that mutual neighborhood commutation.  Even if
every individual model prunes to some cap profile, the profile may depend on
the model; this does not yet produce one computable finite LCS with perfect
completeness.

The recursion-theoretic orientation is otherwise correct.  Culf--Mastel give
perfect CE completeness on `HALT` and a constant CE gap on `NONHALT`, exactly
the orientation required by `re-oriented-lcs-compiler-gives-nonhyperlinear-group`.
What is conditional is the uniform cap-profile compiler, not the Kleene
branch direction.
