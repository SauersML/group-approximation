---
rg: 2
id: gottschalk-via-uniform-single-site-output-law
kind: route
title: A strict automaton would give an injective automaton with a non-uniform site law
target: gottschalk-surjunctivity-conjecture
requires:
  - every-injective-ca-has-uniform-single-site-output-law
  - strict-automata-give-injective-ca-with-skewed-site-marginals
artifacts:
  - research/artifacts/finitary-generation-single-site-criterion-2026-09-12.md
---

Suppose some group carried a strict automaton on `A^G`. The second prerequisite gives an injective
automaton on `(A^(k+1))^G` whose single-site output law is not uniform, contradicting the first
prerequisite. So every group is surjunctive over every alphabet.

This route forms an intended cycle with `uniform-single-site-output-law-from-gottschalk`. The cycle
records an equivalence and establishes neither claim.
