---
rg: 2
id: kl-counterexample-can-be-finitely-presented
kind: claim
title: Any Kervaire--Laudenbach counterexample can be taken finitely presented
distinct_from:
  kl-counterexample-can-be-two-generator-simple: that is the next step of the same chain and consumes this one; this stops at finite presentability, where the coefficient group is still an arbitrary finitely presented group and the collapse rigidity of the simple case is not yet available.
  kl-counterexample-absorbs-any-countable-group: that says a counterexample can be enlarged to contain any prescribed countable group, an upward statement about what cannot be excluded; this says a counterexample can be shrunk to finite presentation data, a downward statement about where to search.
artifacts:
  - research/artifacts/kervaire-laudenbach-audit-2026-08-17.md
---

If `kervaire-laudenbach-nonsingular-conjecture` fails, it fails over a
**finitely presented** coefficient group: there are a finitely presented `P`,
a word `w in P * <t>` with `deg_t(w) != 0`, and a nontrivial `a in P` dying
in `P_w`.

## Why it is worth a node of its own

The conjecture quantifies over all groups, and the first thing one wants to
know about a hypothetical counterexample is whether it must be an infinitary
object.  It need not be.  A counterexample carries finite presentation data
and a finite certificate: the presentation, the word, the element, and the
finite identity `a = prod_j u_j w^{e_j} u_j^{-1}` witnessing the collapse.

## What it does not give

Decidability.  Triviality and normal-closure membership for finitely
presented groups are algorithmically unsolvable, so "finitely presented" here
means "finite input data", not "searchable".  That is why the reduction chain
continues to `kl-counterexample-can-be-two-generator-simple` rather than
stopping here: the simple case is not smaller, it is more rigid.
