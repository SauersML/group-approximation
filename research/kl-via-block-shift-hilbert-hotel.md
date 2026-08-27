---
rg: 2
id: kl-via-block-shift-hilbert-hotel
kind: route
title: Absorb the equation into a shift on infinitely many copies of the coefficients
target: kervaire-laudenbach-nonsingular-conjecture
requires: []
artifacts:
  - research/artifacts/kervaire-laudenbach-audit-2026-08-17.md
---

Represent the coefficient group block-diagonally on `(+)_{j in Z} H_j`, one
faithful copy per block, and look for the root among the block-monomial
operators: a permutation of the blocks carrying arbitrary invertible blocks.
The attraction is the classical swindle — an infinite reservoir of copies,
with the shift moving the discrepancy out to infinity one block at a time —
and it needs no approximation, no metric and no hypothesis on the group.

Dead at the only degree that matters.  By
`block-monomial-root-forces-permutation-order` the block-permutation
homomorphism sends `w(T)` to `sigma^{deg_t(w)}`, so `w(T) = 1` forces
`sigma^m = 1`; at `m = ±1` the root is block-diagonal and the reservoir is
never used.  The shift cannot absorb an equation whose exponent sum is a
unit.

**What survives the demolition.**  At `|m| > 1` the permutation is only
required to be `m`-torsion, so finite-order block rearrangements are not
excluded, and such a counterexample would refute the target and the
hyperlinearity of its coefficient group just as completely as a unimodular
one — it would leave the weak conjecture standing, nothing more.  Nothing
here suggests how to build even that.  What is excluded outright is the free
or bilateral shift, which is the whole point of the construction.
