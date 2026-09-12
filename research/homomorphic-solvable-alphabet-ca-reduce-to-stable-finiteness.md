---
rg: 2
id: homomorphic-solvable-alphabet-ca-reduce-to-stable-finiteness
kind: claim
title: Injective homomorphic automata over finite solvable group alphabets are surjective whenever the relevant group algebras are stably finite
distinct_from:
  stable-finiteness-failure-refutes-surjunctivity: that turns a one-sided pair over F_p[G] into a strict linear automaton; this shows homomorphic automata over any finite solvable alphabet group add no counterexamples beyond the linear ones
artifacts:
  - research/artifacts/strategist-neg-counterexample-plans-2026-09-12.md
---

Let `K` be a finite solvable group and `G` any group. If `M_n(F_p[G])` is directly finite for every `n`
and every prime `p` dividing `|K|`, then every injective cellular automaton `K^G -> K^G` that is a
group homomorphism is surjective. Conversely, a non-directly-finite `M_n(F_p[G])` gives a strict
homomorphic automaton on `(F_p^n)^G`.

So noncommutative group alphabets give no escape from the linear gates. A nonlinear counterexample
must break group structure in the local rule, not only commutativity.

Scope: nonabelian simple composition factors are not covered. On such a layer a homomorphic local rule is
trivial or a coordinate projection composed with an automorphism.

**ESTABLISHED 2026-09-12** by [[homomorphic-solvable-alphabet-ca-reduction-proof]]. Verification requested
from `w4-vf-linear-b`.
