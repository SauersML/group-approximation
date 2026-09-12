---
rg: 2
id: enumerated-isomorphism-is-analytic-complete-citation
kind: claim
title: Isomorphism of computable groups is analytic complete, so no arithmetical classification of it exists
distinct_from:
  isomorphism-to-lamplighter-two-generator-recursive-is-pi2-hard: that gives the arithmetical bounds for finitely generated recursive presentations and a cheap Pi-zero-three lower bound for the enumerated case; this records the external theorem that pins the enumerated case at the analytic level, so no arithmetical completeness is possible there.
  word-problem-solvability-rec2-is-sigma3-complete: that is the third-level classification of a decision problem about one group; this is about a relation between two groups, and it leaves the arithmetical hierarchy entirely.
---

LITERATURE INPUT, source-checked 2026-08-26.

Downey and Montalban, *The isomorphism problem for torsion-free abelian
groups is analytic complete*, J. Algebra 320 (2008) 2291--2300:

> **Theorem 1.2.**  The set of pairs of indices of isomorphic computable
> torsion-free abelian groups is an m-complete `Sigma^1_1` set of natural
> numbers.

They also note (their §4, Theorem 4.1) that isomorphism to the *fixed*
group `Q^infinity` is `Pi^0_3`-complete, and that for torsion-free abelian
groups of fixed finite rank isomorphism is `Sigma^0_3`-complete (Calvert).

**Use here.**  Computable torsion-free abelian groups are in particular
recursively enumerated group presentations, so the isomorphism problem for
enumerated presentations is `Sigma^1_1`-complete.  No arithmetical
classification of it exists, which is the boundary of the ledger
[[arithmetical-complexity-table-of-group-properties]]: every entry there
is a property of a *single* group, and the pattern of arithmetical
completeness does not survive the passage to a relation between two.
Verified against the authors' own preprint copies and the MathSciNet
record; the numbered statements above are quoted, not reconstructed.
