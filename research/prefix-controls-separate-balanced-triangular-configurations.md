---
rg: 2
id: prefix-controls-separate-balanced-triangular-configurations
kind: route
title: Create a common fixed component and separate configurations by an observable orbit
target: balanced-triangular-rule-has-an-invariant-scalar-code
requires: []
artifacts:
  - research/artifacts/gottschalk-balanced-triangular-invariant-scalar-code-construction-2026-09-08.md
---

View the source as a countable product of finite A_4 components,
with distinguished all-one component u. Both Q and F_A preserve
the distinction between u and every other component. Finite
component permutations, explicit prefix homeomorphisms, and
diagonal left A_4 translations generate a countable symmetry
group Lambda commuting with both operations.

A two-component observable reads an x bit when the second
component is u, a y bit when only the first is u, and returns
one otherwise. It satisfies phi(Qz)=phi(z)phi(s^-1z).
The orbit map L(z)(lambda)=phi(lambda^-1z) therefore preserves
the quadratic operation with a right shift by s on Lambda.

For every two distinct inputs, one common symmetry preserves
a differing component and creates a second component equal to
u in both inputs. Place these two components in the observable's
reading positions to distinguish the chosen bit. This proves
injectivity of L. Compactness makes its image closed and its
inverse continuous; equivariance makes that image invariant.
Conjugating F_A gives reversible code dynamics. Ambient full-shift
injectivity requires a further argument and does not follow from
this construction.
