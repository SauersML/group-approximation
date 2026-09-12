---
rg: 2
id: leavitt-rank-three-lift-inverse-support-thirteen
kind: claim
title: Any group-algebra inverse of the rank-three lift has support at least thirteen
distinct_from:
  leavitt-rank-three-unit-lift: that constructs the support-three lift of the Leavitt generators; this is the obstruction saying what a partner for it would have to look like, and rules out every small one.
  bounded-rank-corners-excluded: that is an operator-algebraic bound on the rank of a detecting projection in a relative commutant; this is a combinatorial bound on the support of a group-algebra element, sharing only the word "rank".
artifacts:
  - research/artifacts/kaplansky-direct-finiteness-audit-2026-08-17.md
---

Let `t~ = [u_1] + [u_2] + [u_3]` in `F_2[R^x]` be the support-three lift of
`t_0` from `leavitt-rank-three-unit-lift`.  If `B` in `F_2[R^x]` satisfies

    t~ B = 1,

then `|supp B| >= 13`.

So the smallest conceivable completion of the explicit rank-three lift — the
one that would make `t~` left invertible in the group algebra and start a
counterexample — is excluded, by a wide margin, with no new conjecture.

**SUPERSEDED 2026-08-18, and now vacuous.**
`leavitt-rank-three-lift-has-no-one-sided-inverse` proves there is no such `B`
at **any** support: the support of `t~` generates a subgroup
`(C_2 x C_2) * C_3` of `R^x`
(`leavitt-rank-three-support-group-is-virtually-free`), whose group algebra is
directly finite, and a one-sided inverse cannot escape it
(`subgroup-supported-one-sided-inverse-rigidity`).  This claim is kept because
it is true and because its parity half is still informative, but it should not
be read as "look above thirteen" any more, and the second route
`support-thirteen-from-no-inverse` derives it with no machine enumeration in
the chain.  The same no-go covers the lift of `s_0` and the corner
compression `e t~ e`; see the caveats below, which it settles.

**What it does not say.**  It does not say `B` exists.  It does not bound the
support of a lift of `s_0` (that is `s~`, of support three, and `t~ s~` is
simply not `1`).  And it does not touch the corner formulation
`leavitt-corner-one-sided-lift-exists`, where the relevant identity is
`ab = e` inside `e F_2[R^x] e` rather than `t~ B = 1` in the whole algebra;
transferring the floor across that change of unit is not done here and is not
obvious, since `e` has support two and the corner's elements are constrained
in a way plain support does not see.

**Why it is worth having anyway.**  It converts "nobody has found the missing
factor" into a proved lower bound on where to look, and the bound is imported
from a published exhaustive search rather than from intuition.  It also
predicts the parity: any such `B` has odd support.
