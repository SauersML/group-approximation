---
rg: 2
id: leavitt-unit-group-nonsurjunctive
kind: claim
title: The binary Leavitt unit group is not surjunctive
root: true
distinct_from:
  openai-leavitt-unit-nonsofic: that is the announced nonsoficity of the same group, an external unrefereed input; this is a different property of it, neither implied by nonsoficity nor implying it, and nothing here depends on that announcement
  kl-violating-equation-over-leavitt-unit-group: that asks for a Kervaire--Laudenbach violation over the same group, which would refute its hyperlinearity; this asks for an injective non-surjective cellular automaton, which would refute Gottschalk's conjecture
artifacts:
  - research/artifacts/gottschalk-leavitt-audit-2026-08-17.md
---

Exhibit a finite alphabet `A` and a cellular automaton
`tau : A^G -> A^G` over `G = L_(F_2)(1,2)^x`, the binary Leavitt unit group,
that is **injective and not surjective**.

Since Gottschalk's conjecture asserts that every group is surjunctive, such a
`tau` would refute it.

*Marked `root` because it is a top-level external question, not a step in
this repository's programme: nothing else in this graph depends on it.  It is
here because this repository's object is the only concrete candidate the
question currently has, and because the graph should record where the
repository's Leavitt code does and does not reach.*

## Why this group and not another

Sofic groups are surjunctive (Gromov--Weiss), so any candidate must be
nonsofic; `G` is the one group for which nonsoficity has been announced
(`openai-leavitt-unit-nonsofic`).  That is the **whole** of the connection.
Nonsoficity neither implies nor is implied by non-surjunctivity, and every
statement in the routes below is unconditional — none of them uses the
announcement, and all would read the same if `G` turned out to be sofic.

## The one honest warning

The repository supplies a strict self-embedding of a **proper** invariant
subshift (`leavitt-kernel-annihilator-strict-self-embedding`).  That is not a
step toward this claim: the same construction runs over a finitely generated
free group, which is surjunctive
(`subshift-self-embedding-carries-no-surjunctivity-content`).  The live route
runs through failure of stable finiteness for `F_2[G]`, not through the
subshift.
