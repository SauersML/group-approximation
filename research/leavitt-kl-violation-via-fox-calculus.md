---
rg: 2
id: leavitt-kl-violation-via-fox-calculus
kind: route
title: Select a violating word over the Leavitt unit group by a Fox-derivative computation
target: kl-violating-equation-over-leavitt-unit-group
requires: []
artifacts:
  - research/artifacts/kervaire-laudenbach-audit-2026-08-17.md
---

The cheapest search one can imagine over an explicitly presented group:
enumerate candidate words `w` of exponent sum `m` over `R^x = L_(F_2)(1,2)^x`,
compute Fox derivatives, and keep those whose class generates the
abelianized degree-`m` kernel — the necessary condition for the normal
closure to be everything.  The atlas gives exactly the explicit coordinates
such a computation would need.

Dead: the condition is satisfied by every candidate.  `R^x` is perfect
(`leavitt-gl-equals-el-and-perfect-unit-group`), so by
`degree-kernel-abelianization-is-infinite-cyclic` the abelianized kernel is
`Z` with trivial action and every degree-`m` word maps to a generator.  A
filter that admits all candidates is not a filter.

**What survives the demolition.**  Nothing about the *atlas*, which was
never the problem — the blindness is a property of the invariant, not of the
coordinates it is computed in.  The successor computation is the nonabelian
one recorded on `leavitt-degree-kernel-normally-generated-by-one-word`: a
finite nonabelian quotient of the kernel, or a Peiffer/crossed-module
quotient, in which a candidate's normal closure can actually be seen to be
proper.
