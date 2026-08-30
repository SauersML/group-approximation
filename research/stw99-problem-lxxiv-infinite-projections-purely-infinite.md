---
rg: 2
id: stw99-problem-lxxiv-infinite-projections-purely-infinite
kind: claim
title: A simple unital algebra whose nonzero projections are infinite is purely infinite (STW Problem LXXIV)
root: true
artifacts:
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
  - research/artifacts/stw74-property-sp-cu-stability-audit-2026-08-30.md
---

**Problem LXXIV of Schafhauser--Tikuisis--White, *Nuclear C*-algebras:
99 problems*, arXiv:2506.10902v2.**  Let `A` be a unital simple C*-algebra
(optionally assumed nuclear) such that every nonzero projection in `A` is
infinite.  Must `A` be purely infinite?

The projection-theoretic part is complete: every such projection is actually
properly infinite.  By `stw74-property-sp-is-the-exact-missing-condition`, the
remaining question is precisely whether the displayed hypothesis forces
property (SP).  Thus a counterexample must contain a nonzero hereditary
subalgebra with no nonzero projections.

## Attempts

The live route is `stw74-via-property-sp`.  Fullness of a positive element only
gives a projection below a finite matrix amplification of its hereditary
subalgebra; moving that projection back into the original hereditary algebra is
exactly the step that cannot be inferred from proper infiniteness of the unit.

The strongest current comparison reduction is
`stw74-weak-omega-comparison-closes-hinge`: every separable counterexample
must fail weak omega-comparison, with an explicit witness supported in its full
projectionless corner.  The exact Morita normal form and the stationary
matrix-threshold theorem show that the remaining obstruction persists at one
finite matrix level `m>=2`; it is specifically the failure to descend that
projection to level one.

There is also a comparison-free structural positive class:
`stw74-algebraic-cu-characterizes-pure-infiniteness` proves that, under the
LXXIV hypothesis, `A` is purely infinite exactly when `Cu(A)` is algebraic.
Thus every counterexample has a finite root `x` of the unit whose lower
interval contains no nonzero compact element.
