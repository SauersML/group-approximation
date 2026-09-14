---
rg: 2
id: weak-complexity-rank-one-does-not-imply-rank-one
kind: claim
title: Weak complexity rank one does not imply complexity rank one for Kirchberg algebras
invalidates:
  - trivial-k-rank-one-via-weak-rank-upgrade
distinct_from:
  kirchberg-algebras-have-weak-complexity-rank-one: that is the positive statement that all Kirchberg algebras have weak rank one; this is the negative statement that the weak rank cannot be upgraded to the full rank in general.
artifacts:
  - research/artifacts/stw-uct-reduction-map-2026-09-11.md
---

**ESTABLISHED (literature).**  Jaime--Willett, arXiv:2205.04704v2, Theorem 1.5:
a unital C\*-algebra of complexity rank at most one has torsion-free `K_1`.
Kirchberg algebras with arbitrary countable K-groups exist, for instance a UCT
Kirchberg algebra with `K_1 = Z/2`, and every Kirchberg algebra has weak
complexity rank at most one (`kirchberg-algebras-have-weak-complexity-rank-one`).
So "weak complexity rank one implies complexity rank one" fails on Kirchberg
algebras.  Jaime--Willett compute that a UCT Kirchberg algebra has complexity
rank one exactly when `K_1` is torsion free, and complexity rank two otherwise.

The obstruction is torsion in K-theory.  It says nothing about Kirchberg
algebras with zero K-theory, where both ranks could still coincide.
