---
rg: 2
id: leavitt-group-algebra-not-stably-finite
kind: claim
title: The group algebra of the Leavitt unit group is not stably finite
distinct_from:
  augmentation-blocks-unital-leavitt-family: that is a no-go saying no full binary Leavitt family sits in a matrix ring over an integral group ring; this asks only for a one-sided inverse pair, which is far weaker than a Leavitt family and is not excluded by any argument in this graph
  left-invertible-lift-of-s0-in-leavitt-group-algebra: that pins the one-sided inverse to lie over the Leavitt generator `s_0` under the evaluation map, which is strictly stronger; this asks only that some one-sided inverse pair exists at some finite matrix size
artifacts:
  - research/artifacts/gottschalk-leavitt-audit-2026-08-17.md
---

Exhibit a finite `n >= 1` and matrices `A, B` in `M_n(F_2[G])`, where
`G = L_(F_2)(1,2)^x`, with

    B A = I_n,        A B != I_n.

At `n = 1` this is failure of **Kaplansky direct finiteness** for `F_2[G]`;
at general `n` it is failure of **stable finiteness**.  Either suffices for
`leavitt-unit-group-nonsurjunctive`, via
`stable-finiteness-failure-refutes-surjunctivity`.

## Where the temptation is

The Leavitt relation `t_0 s_0 = 1 != s_0 t_0` is exactly a one-sided inverse
pair — but it lives in the quotient ring `R = L_(F_2)(1,2)`, not in
`F_2[R^x]`, and `s_0, t_0` are not group elements.  The evaluation map
`pi : F_2[G] ->> R` of `leavitt-evaluation-surjective-with-nonzero-kernel` is
surjective, so lifts `a, b` of `s_0, t_0` exist, and they satisfy
`b a - 1 in ker(pi)` and `a b - 1 not in ker(pi)`.  The whole difficulty is
that `b a - 1` need not be `0`.  Concretely, one must solve

    (b a - 1) + b alpha + beta a + beta alpha = 0,     alpha, beta in ker(pi),

and no solution is known.  This is the concrete search form; see
`left-invertible-lift-of-s0-in-leavitt-group-algebra` for the sharp
statement, which also shows the reverse product then fails automatically.

## What is known against it

Nothing in this graph.  The augmentation no-go
(`augmentation-blocks-unital-leavitt-family`) rules out a *full Leavitt
family* in `M_n` over a group ring, and
`leavitt-evaluation-has-no-ring-section` rules out a ring-theoretic section
of `pi`; neither touches a bare one-sided inverse.  External bounded searches
are reported in the audit artifact, unverified here, and are evidence rather
than obstruction.
