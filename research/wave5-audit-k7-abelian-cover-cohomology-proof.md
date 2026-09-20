---
rg: 2
id: wave5-audit-k7-abelian-cover-cohomology-proof
kind: route
title: Three quadratic seventh-root phase vectors stay independent in every other characteristic
target: wave5-audit-k7-abelian-covers-have-only-seven-h1
requires:
  - wave4-visibility-k7-marked-face-presentation
artifacts:
  - research/artifacts/hyperbolic-rf-wave5-audit-2026-09-20.md
---

The artifact proves that any three distinct vectors
`(zeta^(a i+b i^2))_(i in F7)` are linearly independent over any
field containing a primitive seventh root zeta, in characteristic
different from seven. After division by one vector, compare
fibres of the two remaining quadratic exponents. In the
quadratic case this forces proportional exponents. The resulting
four root values have elementary symmetric coefficient
`e_2=-t_0^2`, a unit. This rules out the only remaining possible
trinomial relation; all other cases have too few degrees for
their number of distinct roots.

For a one-dimensional coefficient character of K, averaging on
the finite seven-group vertices makes every vertex cocycle
principal. The six face equations reduce its three primitives
to a linear relation among three such phase vectors. Their
independence forces a single global primitive. Coincident vectors
correspond exactly to a vertex on which the character is trivial;
the unused primitive there has no effect on the cocycle. Thus
first cohomology vanishes in every case.

K_ab=C7^4, so every abelian quotient A is a finite seven-group.
Over an algebraic closure of a field of characteristic not seven,
the regular A-module decomposes into one-dimensional characters.
Finite-index Shapiro therefore gives H^1(N;k)=0. In characteristic
zero this implies N_ab is finite, since N is finitely generated;
in every prime characteristic other than seven it excludes that
prime from N_ab. This proves the integral seven-primary statement.
A solvable finite image of N of order prime to seven has trivial
abelianization and must itself be trivial, proving the refinement
restriction.
