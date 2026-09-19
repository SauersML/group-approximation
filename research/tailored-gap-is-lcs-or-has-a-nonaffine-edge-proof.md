---
rg: 2
id: tailored-gap-is-lcs-or-has-a-nonaffine-edge-proof
kind: route
title: Present each affine edge relation by parity rows and otherwise invoke ternary closure
target: tailored-gap-is-lcs-or-has-a-nonaffine-edge
requires:
  - perfect-lcs-gap-implies-nonhyperlinear
  - affine-nested-odd-xor-selectors-force-affine-behavior
---

Every affine subset of a finite-dimensional vector space over `F_2` is the
solution set of a finite system of affine linear equations.  If every
positive-weight `A_e` is affine, choose such a system for each edge.  These are
precisely binary LCS decision predicates on the original full answer bits.
Forgetting which coordinates were called readable changes neither the game
predicate nor any correlation, so both displayed values of `G` are unchanged.
The first alternative and `perfect-lcs-gap-implies-nonhyperlinear` follow.

If the first alternative fails, some positive-weight `A_e` is nonaffine.
Ternary closure characterizes nonempty affine subsets of `F_2^N`, so there are
accepted full answers `a,b,c in A_e` with

```text
a+b+c notin A_e.
```

Three singleton-complete labels carrying these independent scalar payloads
have a feasible three-label activation under any commuting affine nested
selector gadget, but their odd-XOR aggregate is rejected.  This is exactly
the scalar countermodel from
`affine-nested-odd-xor-selectors-force-affine-behavior`.
