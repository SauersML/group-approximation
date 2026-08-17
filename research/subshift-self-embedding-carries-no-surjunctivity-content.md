---
rg: 2
id: subshift-self-embedding-carries-no-surjunctivity-content
kind: claim
title: A strictly embedded proper subshift says nothing about surjunctivity
invalidates: [nonsurjunctive-by-extending-the-subshift-automaton]
artifacts:
  - research/artifacts/gottschalk-leavitt-audit-2026-08-17.md
  - GroupApproximation/Leavitt/UnitAdditiveSpan.lean
---

There is a **finitely generated free group** `F` admitting a surjective
unital ring homomorphism `pi : F_2[F] ->> L_(F_2)(1,2)` with nonzero kernel,
and hence — by the identical construction — a proper closed `F`-invariant
linear subshift `X ( F_2^F` carrying an explicit finite-memory linear
cellular automaton that is injective and not surjective.

Free groups are residually finite, hence sofic, hence surjunctive by
Gromov--Weiss.  So the premises of
`leavitt-kernel-annihilator-strict-self-embedding` hold over a group whose
surjunctivity is *known*, and the inference

    strict self-embedding of a proper invariant subshift  =>  not surjunctive

is a non-sequitur with an explicit counterexample.  No choice of lift or
alphabet repairs it.

## Why this is stronger than the parity observation

The natural four-unit lift `a = [uv] + [u] + [v] + [w]` has `eps(a) = 0`, so
right multiplication by it misses `1` and its dual `T_a` is not injective on
the full shift.  That kills one lift.  This claim kills the shape of the
argument: the subshift data is compatible with surjunctivity, so it can carry
no surjunctivity information whatever, however the lift is chosen.

Half of it needs no external input at all: `F_2[F]` is a domain for `F` free
(free groups are biorderable), hence directly finite, so the subshift data
cannot even imply failure of direct finiteness — the property that
`stable-finiteness-failure-refutes-surjunctivity` actually consumes.
Gromov--Weiss is used only for the sharper phrasing above.

## The ring-level twin

`direct-finiteness-not-inherited-by-quotients` is the same lesson one level
down: the surjection `F_2[R^x] ->> R` exhibits the defect in a *quotient*,
which is the direction direct finiteness does not travel, and the witness
there is `k<X,Y>/(XY-1)`.  This claim is its dynamical form, with a free group
in place of a free algebra.  A write-up that reads either the subshift or the
quotient as a counterexample has the same gap twice.

## What survives

The subshift theorem remains a correct and explicit theorem about
`L_(F_2)(1,2)^x`.  It is simply a statement about a quotient ring's module
theory wearing dynamical clothes, and the surjunctivity question lives
entirely in the group algebra `F_2[R^x]`, which the quotient cannot see.
