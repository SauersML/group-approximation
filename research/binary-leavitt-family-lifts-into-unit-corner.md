---
rg: 2
id: binary-leavitt-family-lifts-into-unit-corner
kind: claim
title: The Leavitt family itself lifts into the corner of the unit group algebra
distinct_from:
  leavitt-corner-one-sided-lift-exists: that asks only for one pair with ab = e and a surviving defect; this asks for all four generators with all five relations, a strictly stronger and more rigid demand, and it is stated separately because a family is what a construction would naturally produce.
  augmentation-blocks-unital-leavitt-family: that proves no unital binary Leavitt family exists wherever a unital map to a domain does, in particular in Z[G] and in every M_n(Z[G]); this asks for one in a corner of F_2[R^x] chosen precisely so that no such map exists.
  binary-leavitt-algebra-not-directly-finite: that is the established fact that the relations hold somewhere, namely in the Leavitt algebra; this asks for a copy of them in a corner of a group algebra, which is the hard direction and is open.
  leavitt-unit-group-algebra-not-directly-finite: that is the conclusion this would produce, failure of direct finiteness for F_2[R^x]; this is one strictly stronger hypothesis that would produce it, and the conclusion could hold with no family anywhere.
  leavitt-group-algebra-not-stably-finite: that is the matrix-level failure statement, an existential over one-sided inverse pairs at some size; this asks for four specific elements satisfying five equations in one fixed corner at size one.
  leavitt-unit-group-nonsurjunctive: that is a dynamical statement about cellular automata on the full shift over the same group; this is an algebraic lifting demand inside a corner of its group algebra, and it reaches that node only through the stable-finiteness claim.
  leavitt-gl-equals-el-and-perfect-unit-group: that is an established K-theoretic identification inside the unit group of the Leavitt algebra; this is an open lifting problem in the group algebra of that unit group, one level up.
artifacts:
  - research/artifacts/kaplansky-direct-finiteness-audit-2026-08-17.md
---

With `A = F_2[R^x]`, `e = [g] + [g^2]`, `pi_e : eAe ->> R` as in
`leavitt-corner-idempotent-unital-surjection`: exhibit `S_0, S_1, T_0, T_1` in
`eAe` with

    T_i S_j = delta_ij e,        S_0 T_0 + S_1 T_1 = e,

and `pi_e(S_i) = s_i`, `pi_e(T_i) = t_i`.

Equivalently — and this is the cleaner way to say it — exhibit a unital ring
**section** `R -> eAe` of `pi_e`.  A section carries the family over
automatically, and conversely a family lifting the generators generates a
section, since the Leavitt algebra is presented by exactly those relations.

## Relation to the repository's own no-go

`augmentation-blocks-unital-leavitt-family` is the reason this is stated in a
corner and not anywhere more comfortable.  Its scalar half needs only a unital
map to a domain, so it forbids such a family in `Z[G]`, in `F_2[G]`, and in
`fAf` for every idempotent `f` of augmentation one.  The corner at `e` has
`eps(e) = 0` and is not covered.  That is the entire reason to believe the
question is open rather than closed — it is not evidence that a family exists.

## Honest assessment

Strictly stronger than `leavitt-corner-one-sided-lift-exists`, and stronger
than the conjecture being false: a section of `pi_e` would make `R` a retract
of a corner of a group algebra, which is a considerably more structured
statement than the mere failure of direct finiteness.  It is listed because
the only concrete way anyone has proposed to produce the pair `(a,b)` is to
produce the family and read the pair off it, and because it fails or succeeds
for reasons one can look for — a section is a rigid object with a Leavitt
normal form on one side.
