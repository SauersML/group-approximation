---
rg: 2
id: stw96-real-rank-zero-single-generation-frontier
kind: claim
title: Every separable real-rank-zero C*-algebra is singly generated
root: true
distinct_from:
  stw96-simple-stable-rank-one-single-generation-frontier: real rank zero is a different regularity condition and this formulation does not assume simplicity.
artifacts:
  - research/artifacts/stw96-regular-rank-single-generation-audit-2026-08-30.md
---

Does every separable real-rank-zero C*-algebra have a single generator?

This remains open.  The Elliott--Li--Niu counterexample has real rank at least
two.  Their Remark 3.4 explicitly asks this real-rank-zero question.  Positive
results for AF algebras and for real-rank-zero Z-stable algebras do not settle
the unrestricted statement.

## Attempts

Approximating self-adjoint elements by finite-spectrum elements does not
approximate finite sets by finite-dimensional subalgebras, so the AF
single-generator theorem does not extend from real rank zero alone.  The
known counterexample mechanism also fails to enter this class: the planar
homology obstruction in Elliott--Li--Niu simultaneously forces real rank at
least two.  No replacement obstruction compatible with real rank zero is
currently known.

There are now two rigorous reductions.  First,
`stw96-quotient-obstructions-preserve-rank-defects` shows that quotient-based
obstruction transfer cannot construct the first example, since real rank zero
passes to quotients.  Second,
`stw96-rr0-nowhere-scattered-generator-corridor` proves a positive theorem on
the nowhere-scattered part: finite nuclear dimension with no purely infinite
simple subquotient gives generator rank one; in particular finite decomposition
rank suffices.  Nuclear purely infinite real-rank-zero algebras also have
generator rank one, so the remaining finite-nuclear-dimension residue must have
a purely infinite simple subquotient while the total algebra is not purely
infinite.  The unrestricted real-rank-zero frontier remains open beyond this
corridor.
