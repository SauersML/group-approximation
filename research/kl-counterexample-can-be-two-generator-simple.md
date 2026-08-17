---
rg: 2
id: kl-counterexample-can-be-two-generator-simple
kind: claim
title: Any Kervaire--Laudenbach counterexample can be taken two-generator simple
distinct_from:
  kl-counterexample-can-be-finitely-presented: that is the previous step of the same chain and is consumed by this one; it stops at an arbitrary finitely presented coefficient group, where none of the simple-case rigidity is available.
  kl-counterexample-absorbs-any-countable-group: that adds a prescribed countable subgroup to the simple envelope, which is an obstruction to classifying counterexamples; this is the reduction itself, and is what that node amplifies.
artifacts:
  - research/artifacts/kervaire-laudenbach-audit-2026-08-17.md
---

If `kervaire-laudenbach-nonsingular-conjecture` fails, it fails over a
two-generator nonabelian **simple** coefficient group.

Consequently the conjecture holds for all groups if and only if it holds for
two-generator nonabelian simple groups —
`kl-holds-over-two-generator-simple-groups` — and by
`kl-simple-failure-leaves-only-the-cyclic-quotient` that restricted statement
is a single, very rigid normal-generation problem.

## Why the restriction is worth having

The unrestricted conjecture is a statement about an arbitrary group and an
arbitrary word, with a coefficient element to protect.  After this reduction
there is no coefficient element to choose: a failure kills the entire
coefficient group and leaves exactly `C_|m|`.  The search space collapses from
"some element dies" to "one word normally generates a specific kernel", which
is what makes the remaining problem statable in one line.

## What it costs

Contact with any structure the original coefficient group had.  A simple
envelope destroys presentations, residual properties, orderability, growth,
and every approximation property this repository normally reasons with;
`kl-counterexample-absorbs-any-countable-group` shows that the loss is not an
artefact of the construction but a genuine feature of the problem.  In
particular, this reduction is of no use for deciding whether a *particular*
group — the binary Leavitt unit group, say — violates the conjecture.  For
that lane the useful direction is the converse one recorded on
`kl-simple-failure-leaves-only-the-cyclic-quotient`, which needs no
simplicity at all.
