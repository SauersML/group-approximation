---
rg: 2
id: leavitt-unit-group-nonsurjunctive
kind: claim
title: The binary Leavitt unit group is not surjunctive
root: true
distinct_from:
  openai-leavitt-unit-nonsofic: that is the nonsoficity of the same group; this is a different property of it, neither implied by nonsoficity nor implying it
  leavitt-unit-group-algebra-not-directly-finite: that is the Kaplansky question for the same group's modular group algebra, a statement about elements of a ring; this is a statement about cellular automata on a full shift, and while the first implies the second the converse is not available
  kl-violating-equation-over-leavitt-unit-group: that asks for a Kervaire--Laudenbach violation over the same group, which would refute its hyperlinearity; this asks for an injective non-surjective cellular automaton, which would refute Gottschalk's conjecture
artifacts:
  - research/artifacts/gottschalk-leavitt-audit-2026-08-17.md
---

Exhibit a finite alphabet `A` and a cellular automaton
`tau : A^G -> A^G` over `G = L_(F_2)(1,2)^x`, the binary Leavitt unit group,
that is **injective and not surjective**.

Since Gottschalk's conjecture asserts that every group is surjunctive, such a
`tau` would refute it.

*Marked `root` because it heads a lane of its own, exactly as
`leavitt-unit-group-algebra-not-directly-finite` does: it is a top-level
external question, not a step toward `q3-4-resolved`, and no route should be
built from it toward that goal.  It is recorded because this repository's
object is the only concrete candidate the question currently has, and because
the graph should say where the Leavitt code does and does not reach.*

## Why this group and not another

Sofic groups are surjunctive (Gromov--Weiss), so any candidate must be
nonsofic, and `G` is the one group for which nonsoficity has been announced
(`openai-leavitt-unit-nonsofic`).  That is the **whole** of the connection.
Nonsoficity neither implies nor is implied by non-surjunctivity, and every
statement in the routes below is unconditional — none uses the announcement,
and all would read the same if `G` turned out to be sofic.

## Relation to the Kaplansky lane

This claim sits strictly downstream of
`leavitt-unit-group-algebra-not-directly-finite`: a one-sided inverse in
`F_2[G]` yields the automaton
(`stable-finiteness-failure-refutes-surjunctivity`), so everything in that
lane — the corner construction, the lifting problems, the support-thirteen
floor — is evidence about this question too.  Nothing runs back the other way.

## The one honest warning

The repository supplies a strict self-embedding of a **proper** invariant
subshift (`leavitt-kernel-annihilator-strict-self-embedding`).  That is not a
step toward this claim: the same construction runs over a finitely generated
free group, which is surjunctive
(`subshift-self-embedding-carries-no-surjunctivity-content`).  It is the
dynamical twin of `direct-finiteness-not-inherited-by-quotients`, and both
kill the same shortcut.
