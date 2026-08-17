---
rg: 2
id: stable-finiteness-failure-refutes-surjunctivity-proof
kind: route
title: Dualize right multiplication on the free module of rank n
target: stable-finiteness-failure-refutes-surjunctivity
requires: []
artifacts:
  - research/artifacts/gottschalk-leavitt-audit-2026-08-17.md
---

## Why sufficient

Write `S = k[G]` and view `S^n` as row vectors, a free **left** `S`-module.
Right multiplication

    R_A : S^n -> S^n,     v |-> v A

is left `S`-linear, since scalars act on the left.

*Surjective.*  `R_A(R_B(v)) = v B A = v`, so `R_A . R_B = id`.

*Not injective.*  If it were, then from `R_A . R_B . R_A = R_A` one may
cancel the injective `R_A` on the left, giving `R_B . R_A = id`, i.e.
`v A B = v` for all `v`, i.e. `A B = I_n`, contrary to hypothesis.

*Dualize.*  `S^n` is the direct sum of one copy of `k^n` per element of `G`,
so its full algebraic `k`-dual is the product `(k^n)^G`, the full shift over
the finite alphabet `k^n`; the dual of left multiplication by `[h]` is the
shift by `h`, so `R_A^*` is `G`-equivariant.  Each entry of `A` has finite
support, so `(R_A^* x)(g)` reads only the finitely many coordinates `g s` for
`s` in the union of those supports: `R_A^*` is continuous with finite memory,
hence a cellular automaton.

Over a field, a linear map `f` is surjective if and only if `f^*` is
injective, and injective if and only if `f^*` is surjective — for the second
direction, a functional that is nonzero on `ker f` lies outside the image of
`f^*`, and a proper subspace always carries such a functional.  Applying both
to `R_A`: `R_A^*` is injective and not surjective.

That is an injective non-surjective cellular automaton on a full shift over a
finite alphabet, so `G` is not surjunctive.
