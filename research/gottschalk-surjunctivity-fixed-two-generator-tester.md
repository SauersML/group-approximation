---
rg: 2
id: gottschalk-surjunctivity-fixed-two-generator-tester
kind: claim
title: One two-generator finitely presented group tests Gottschalk's surjunctivity conjecture
distinct_from:
  leavitt-unit-group-nonsurjunctive: that asks for an explicit counterexample on one specially motivated unit group; this reduces the universal conjecture exactly to one fixed finitely presented host.
  stable-finiteness-failure-refutes-surjunctivity: that gives a sufficient linear-algebraic route to a counterexample; this treats arbitrary finite-alphabet cellular automata and proves an iff tester.
  universal-local-approximation-fixed-two-generator-test-group: that tests metric finite-table approximation properties; surjunctivity is a rigidity property of full-shift cellular automata and requires a separate compactness argument.
  luck-determinant-fixed-two-generator-tester: that tests a Fuglede--Kadison determinant inequality; this tests Gottschalk's dynamical conjecture.
---

A group `G` is **surjunctive** if, for every finite alphabet `A`, every
injective cellular automaton

~~~text
tau:A^G -> A^G
~~~

is surjective.

There exists one fixed two-generator finitely presented group `U` such that

~~~text
U is surjunctive
  <=>
every group is surjunctive.
~~~

Thus Gottschalk's conjecture has exactly the same truth value as
surjunctivity of this one group. The host is the torsionful all-group host
in [[universal-all-group-subgroup-colimit-class-tester]], with
`Tord(U)={2,3,4,...}`. It is fixed independently of the alphabet and local
rule.

This is an exact reduction only. It neither asserts that `U` is
surjunctive nor produces a nonsurjunctive automaton on it.

**ESTABLISHED 2026-08-31** by
[[gottschalk-surjunctivity-fixed-tester-proof]].
