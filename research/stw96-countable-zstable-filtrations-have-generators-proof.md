---
rg: 2
id: stw96-countable-zstable-filtrations-have-generators-proof
kind: route
title: Glue Z-stability through successor extensions and countable limit stages
target: stw96-countable-zstable-filtrations-have-generators
requires: []
---

We prove by transfinite induction that every `I_beta` is `Z`-stable.  The zero
algebra at the initial stage absorbs `Z`.  At a successor stage there is an
exact sequence

`0 -> I_alpha -> I_(alpha+1) -> I_(alpha+1)/I_alpha -> 0`.

The ideal is `Z`-stable by induction and the quotient is `Z`-stable by
hypothesis.  Toms--Winter, [Theorem
4.3](https://arxiv.org/abs/math/0502211), says that absorption of a
`K_1`-injective strongly self-absorbing algebra passes from the ideal and
quotient to a separable extension.  The Jiang--Su algebra has the required
properties, so `I_(alpha+1)` is `Z`-stable.

Let `beta` be a nonzero limit stage.  Since `beta` is a countable ordinal, it
has an increasing cofinal sequence `(alpha_n)`.  Continuity of the filtration
identifies `I_beta` with the sequential inductive limit of the inclusions
among the `I_(alpha_n)`.  Each term is `Z`-stable by induction, and
Toms--Winter, Corollary 3.4, says that `Z`-stability passes to sequential
inductive limits of separable C*-algebras.  Hence `I_beta` is `Z`-stable.
This completes the induction and proves that `A = I_gamma` is `Z`-stable.
Hannes Thiel, [Theorem
5.3](https://arxiv.org/abs/2006.08404), now applies to the separable,
real-rank-zero algebra `A` and gives generator rank one, with generators a
dense `G_delta`: here a pair of self-adjoints `(x,y)` is identified with the
single element `x+iy` of `A`.

For the stated consequence, finite nuclear dimension passes to ideals and
quotients.  Nowhere scatteredness is equivalent to the absence of nonzero
elementary ideal-quotients by Thiel--Vilalta, [Theorem
3.1](https://arxiv.org/abs/2112.09877).  Thus every simple successor quotient
is non-elementary, separable, and of finite nuclear dimension.  Tikuisis,
[Corollary 8.7](https://arxiv.org/abs/1210.2237), makes each such quotient
`Z`-stable, so the first part applies.

Finally, if `A` has finitely many ideals, repeated choice of a maximal proper
ideal produces a finite composition series with simple successor quotients.
This last finite-ideal `Z`-stability step is also exactly Tikuisis, Corollary
8.7; the argument above records why mixed purely infinite/stably finite layers
cause no extension loss before Thiel's generator theorem is applied.
