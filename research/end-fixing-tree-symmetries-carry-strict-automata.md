---
rg: 2
id: end-fixing-tree-symmetries-carry-strict-automata
kind: claim
title: The amenable non-unimodular symmetry group of a tree with a fixed end carries a strict injective automaton
distinct_from:
  certificate-controlled-routing-is-surjunctive: that proves surjunctivity for routing rules over every group through balance of reads; this exhibits a transitive amenable but non-unimodular symmetric space where a local copying rule is strict, so balance is what a positive proof must use.
  strict-automaton-lowers-bernoulli-rokhlin-entropy: that bounds the entropy of Bernoulli shifts over a group carrying a strict automaton; this is a calibration off groups, where the index set is a homogeneous space of a non-unimodular group.
artifacts:
  - research/artifacts/gottschalk-tree-calibration-and-bernoulli-preservation-2026-09-12.md
---

Let `T` be the 3-regular tree, `xi` an end of `T`, and `p(v)` the neighbour of `v`
toward `xi`. `Gamma = Aut(T, xi)` acts transitively on vertices. It is amenable,
being an increasing union of compact open subgroups extended by `Z`, and it is not
unimodular.

For a totally ordered finite alphabet, `tau(x)(v) = x(p(v))` is a continuous,
`Gamma`-equivariant, local, injective map of `A^V` that is not surjective. Its
decoder `sigma(y)(w) = min(y(c), y(c'))` over the two children satisfies
`sigma tau = id`. Two siblings with different symbols form a Garden of Eden.

**Calibration.** Amenable symmetry and local geometry do not force surjectivity.
Over a group acting on itself, equivariant maps of the index set are bijections
`g -> g m`, so this copying mechanism is absent. Positive proofs must use group
structure: unimodularity or mass-transport balance, invariance of the uniform
measure, or finite models.

**ESTABLISHED 2026-09-12** by
[[end-fixing-tree-symmetries-carry-strict-automata-proof]].
