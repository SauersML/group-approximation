---
rg: 2
id: quantum-transfer-via-topological-absorption
kind: route
title: Turn a strict automaton into a topological Bernoulli absorption, then read the absorption as a strict monomial quantum automaton
target: strict-automata-yield-strict-quantum-endomorphisms
requires:
  - strict-automata-yield-topological-bernoulli-absorptions
  - monomial-quantum-automata-are-topological-bernoulli-absorptions
---

Let `G` carry an injective, non-surjective automaton.
1. By `strict-automata-yield-topological-bernoulli-absorptions`, there are a finite alphabet `A`, `d = |A|`,
   and an absorption `A^G -> A^G x Y` with `|Y| >= 2`.
2. By (2) implies (1) of `monomial-quantum-automata-are-topological-bernoulli-absorptions`, with `A` replaced by
   `Z/d` (only `|A|` matters there), `(x)_G M_d` carries a strict monomial diagonal-preserving quantum automaton.
   It is a shift-equivariant, finite-propagation, unital *-endomorphism that is not onto.

This is the target with this `d`.
