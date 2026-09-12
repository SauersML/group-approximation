---
rg: 2
id: leavitt-direct-finiteness-from-both-lifting-problems-failing
kind: route
title: If neither normal form has a witness then the Leavitt unit group algebra is directly finite
target: leavitt-unit-group-algebra-is-directly-finite
requires:
  - no-left-invertible-lift-of-s0-in-leavitt-group-algebra
  - leavitt-evaluation-kernel-unitization-directly-finite
  - leavitt-inverse-defects-are-visible-or-invisible
artifacts:
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/leavitt-inverse-defect-normal-forms-2026-09-12.md
---

## Why sufficient

Suppose `b a = 1 != a b` in `F_2[R^x]`. By
`leavitt-inverse-defects-are-visible-or-invisible`, a group-element translate of
the pair lies either over `(s_0, t_0)` or over `(1, 1)`.

* The first case is a left-invertible lift of `s_0`, excluded by the first
  prerequisite.
* The second case is a failure of direct finiteness in `F_2 1 + ker(pi)`,
  excluded by the second.

So no such pair exists.

*Verified independently by `gk-vf-linear` (2026-09-12): exhaustiveness comes from the established normal forms, so the route is valid. See Section 5 of the linear-family verification artifact.*

## An intended cycle (2026-09-12)

With `kernel-unitization-df-from-unit-group-algebra-df` this route closes a deliberate
equivalence cycle between direct finiteness of `F_2 1 + ker(pi)` and direct finiteness of the
whole group algebra. The cycle warning it draws is informational. Every node on the cycle is
OPEN, so nothing is established through it.

The kernel-corner transfer (`leavitt-kaplansky-failures-have-invisible-witnesses`) makes the
first prerequisite unnecessary for this target: `leavitt-df-from-kernel-unitization-df` needs
only the second. This route stays valid.
