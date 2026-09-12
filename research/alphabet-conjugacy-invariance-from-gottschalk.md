---
rg: 2
id: alphabet-conjugacy-invariance-from-gottschalk
kind: route
title: A conjugacy onto a smaller full shift followed by the symbol inclusion is a strict automaton
target: full-shifts-with-different-alphabets-are-not-conjugate
requires:
  - gottschalk-surjunctivity-conjecture
artifacts:
  - research/artifacts/gottschalk-rokhlin-entropy-route-2026-09-12.md
  - research/artifacts/gk-p-inf-wild-borel-and-topological-2026-09-12.md
---

Proposition 3.1 of the artifact.

1. Let `phi: A^G -> B^G` be a conjugacy. Using `phi^-1` if needed, assume `|A| > |B|`, and fix an
   injection `B -> A` inducing `iota: B^G -> A^G`.
2. `iota o phi` is continuous, equivariant and injective, so by Curtis–Hedlund–Lyndon it is a
   cellular automaton on `A^G`.
3. Its image lies in the proper closed set `iota(B^G)`, so it is not surjective. This contradicts
   surjunctivity of `G`.

The same argument works group by group: surjunctivity of `G` alone suffices.

**Redundant (2026-09-12).** The target is established directly by
`full-shifts-with-different-alphabets-are-not-conjugate-proof`: a conjugacy bijects the constant
configurations. This route stays only as a record that the topological conclusion is too weak to
separate the goal from anything.
