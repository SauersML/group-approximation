---
rg: 2
id: surjunctive-guard-subgroups-force-surjectivity
kind: claim
title: An injective cellular automaton preserving unions of surjunctive subgroup cosets is surjective
artifacts:
  - research/artifacts/gottschalk-surjunctive-guard-finite-intersection-proof-2026-09-08.md
---

Let G be any group, A a finite nonempty alphabet with distinguished
symbol 0, and H a surjunctive subgroup of G. Suppose an injective
cellular automaton F:A^G -> A^G preserves configurations supported
in every union of left cosets gH. Then F is surjective.

Equivalently, assume F(x)(g)=0 whenever x vanishes on gH. For finite
memory S, it is enough that H_0=<S intersect H> be surjunctive;
the support condition descends to H_0.

No commensuration, amenability, finite generation, or subgroup-rank
condition is required. The hypothesis concerns the guard, not the
ambient group. In particular this does not prove Gottschalk for G:
taking H=G would require the unresolved surjunctivity hypothesis
itself. Free guards and the preceding abelian and polycyclic guard
results are covered.
