---
rg: 2
id: leavitt-group-algebra-not-stably-finite
kind: claim
title: The group algebra of the Leavitt unit group is not stably finite
distinct_from:
  leavitt-unit-group-algebra-not-directly-finite: that is the scalar case `n = 1`, the Kaplansky question proper, and it heads its own lane; this is the matrix statement at some unspecified finite size, which is what the surjunctivity criterion actually consumes. The two are interderivable for this group by `leavitt-stable-finiteness-equals-direct-finiteness`, established 2026-08-17, but they remain different statements and each keeps its own lane
  stable-finiteness-reduces-to-prime-field: that fixes which coefficient fields a search must cover, for every group at once; this is the failure demanded of one group over the prime field, and that node is the reason `F_2` here costs nothing
  augmentation-blocks-unital-leavitt-family: that is a no-go saying no full binary Leavitt family sits in a matrix ring over an integral group ring; this asks only for a one-sided inverse pair, which is far weaker than a Leavitt family and is not excluded by any argument in this graph
artifacts:
  - research/artifacts/gottschalk-leavitt-audit-2026-08-17.md
---

Exhibit a finite `n >= 1` and matrices `A, B` in `M_n(F_2[G])`, where
`G = L_(F_2)(1,2)^x`, with

    B A = I_n,        A B != I_n.

This is failure of **stable finiteness** for `F_2[G]`.  It is what
`stable-finiteness-failure-refutes-surjunctivity` consumes, and hence the
immediate prerequisite of `leavitt-unit-group-nonsurjunctive`.

## Its place between the two lanes

At `n = 1` this is `leavitt-unit-group-algebra-not-directly-finite`, the
Kaplansky question, and every route currently aimed here goes through that
node — a scalar witness is a matrix witness.  The statement is kept at general
`n` because the surjunctivity criterion is.

**The converse holds too, for this group (2026-08-17).**  This paragraph used
to say that nothing in the graph reduces the matrix problem to the scalar one,
and that a witness at some `n >= 2` would refute Gottschalk's conjecture for
`G` without deciding Kaplansky's direct-finiteness conjecture.  Both are now
false.  `leavitt-stable-finiteness-equals-direct-finiteness` compresses a
failure at any `n` back to `n = 1`, using the corner copies of
`M_(2^k)(F_2[G])` that the Leavitt self-similarity puts inside `F_2[G]`
(`leavitt-matrix-amplification-in-unit-group-algebra`); the route
`leavitt-direct-finiteness-failure-from-matrix-failure` draws that direction.
So this claim and the Kaplansky claim are interderivable, Gottschalk for `R^x`
and Kaplansky for `F_2[R^x]` stand or fall together, and no search needs to
range over `n`.

The general fact is unchanged: for group algebras over a field, direct and
stable finiteness are not known to be equivalent, and the char-`0` theorem
quoted in `official/counterexample.tex` is stated in the stronger stable form
for that reason.  What is new is specific to this self-similar group and does
not transport.

By `stable-finiteness-reduces-to-prime-field`, restricting to `F_2` rather
than to an arbitrary field of characteristic two costs nothing.

## What is known against it

Nothing decisive, in either direction.  All constraints live at `n = 1`, and
after the equivalence above that is no longer a limitation of what has been
looked for — it is where the whole question is.
`leavitt-rank-three-lift-inverse-support-thirteen` excludes the smallest
completions of the explicit generator lift, and
`direct-finiteness-not-inherited-by-quotients` explains why the surjection
onto the Leavitt algebra supplies nothing by itself.  No obstruction is known
at any `n >= 2`, and by the equivalence none can be that is not already an
obstruction at `n = 1`.
