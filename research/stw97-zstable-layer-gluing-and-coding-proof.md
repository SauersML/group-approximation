---
rg: 2
id: stw97-zstable-layer-gluing-and-coding-proof
kind: route
title: Glue Z-absorption through the filtration and invoke unital generator coding
target: stw97-unital-countable-zstable-layers-are-singly-generated
requires: []
artifacts:
  - research/artifacts/stw96-xcvi-xcvii-literature-audit-2026-08-30.md
---

We first prove by transfinite induction that every `I_beta` is Z-stable.  The
claim is harmless at `beta=0`.  At a successor stage, both terms at the ends
of

```text
0 -> I_alpha -> I_(alpha+1) -> I_(alpha+1)/I_alpha -> 0
```

are Z-stable, the ideal by induction and the quotient by hypothesis.
Toms--Winter, [*Strongly self-absorbing C-star
algebras*](https://arxiv.org/abs/math/0502211), Theorem 4.3, proves that
absorption of a `K_1`-injective strongly self-absorbing algebra passes from an
ideal and quotient to the separable extension.  The Jiang--Su algebra has
these properties, so `I_(alpha+1)` is Z-stable.

If `beta` is a nonzero limit ordinal, countability gives an increasing
cofinal sequence `(alpha_n)`.  Continuity identifies `I_beta` with the
sequential inductive limit of the `I_(alpha_n)`.  Toms--Winter, Corollary 3.4,
says that absorption passes to such inductive limits.  Hence `I_beta` is
Z-stable.  The induction ends with `A=I_gamma` Z-stable.

The point where unitality replaces the real-rank-zero hypothesis used in the
XCVI corridor is Thiel--Winter, [*The generator problem for Z-stable C-star
algebras*](https://arxiv.org/abs/1201.3879), Theorem 3.7: every unital
separable Z-stable C-star algebra is singly generated.  Applying it to `A`
proves the first assertion.  This only gives existence of a generator; it
does not claim that generators are dense.

For the finite-nuclear-dimension consequence, nuclear dimension passes to
ideals and quotients, while nowhere scatteredness passes to subquotients.
Thus every simple successor quotient is separable, non-elementary, and of
finite nuclear dimension.  Tikuisis, [*Nuclear dimension, Z-stability, and
algebraic simplicity for stably projectionless C-star
algebras*](https://arxiv.org/abs/1210.2237), Corollary 8.7, makes each such
quotient Z-stable, and the first part applies.

Finally, a C-star algebra with finitely many ideals has a finite composition
series with simple successor quotients: choose a maximal proper ideal,
iterate inside it, and use finiteness to terminate.  If `A` is nowhere
scattered, none of these nonzero simple subquotients is elementary.  This
proves the last assertion.

**Trust boundary.**  Single generation is not being passed directly through
extensions; that permanence is false in general.  What passes through each
extension and countable limit is Z-absorption, after which the unital
Thiel--Winter coding theorem is applied once to the total algebra.  The
unitality of `A` is essential to this final cited theorem, and no generator-
rank-one conclusion is asserted.
