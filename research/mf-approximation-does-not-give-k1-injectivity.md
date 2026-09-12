---
rg: 2
id: mf-approximation-does-not-give-k1-injectivity
kind: claim
title: An MF algebra can fail K1-injectivity
distinct_from:
  stw59-simple-ah-non-k1-injective: that is the failure of K_1-injectivity for the AH algebra, with no approximation content; this adds that the same algebra is MF, so matrix approximation is compatible with that failure.
  unit-abelianization-to-algebraic-k1-not-injective: that compares the unit-group abelianization with algebraic K_1; this compares matrix approximability with the topological component group.
  amenable-implies-operator-mf: that is the group-level import for amenable groups; this is a C-star-level observation about one AH algebra and the unitary subgroups it carries.
artifacts:
  - research/artifacts/ah-k1-mf-bridge-2026-09-07.md
---

The algebra `A` of `stw59-simple-ah-non-k1-injective` is MF, so every
countable subgroup of `U(A)` is an MF group, while

```text
U(A)/U_0(A) = Z/2,      K_1(A) = 0.
```

So MF approximability does not imply `K_1`-injectivity.

There is no tension with the non-MF programme.  Matrix models preserve the
norm and the algebraic relations of a finite set without preserving whether a
unitary can be joined to the identity **inside** `A`; the connecting paths
available in the matrix models need not come from paths in `A`.
