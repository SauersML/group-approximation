---
rg: 2
id: every-group-is-torus-surjunctive
kind: claim
title: Over every group, every injective continuous equivariant self-map of every torus full shift is surjective
distinct_from:
  gottschalk-surjunctivity-conjecture: that is surjunctivity for finite alphabets; this is the analogue for the connected alphabets T^d, where cohomological degree is available and finite-model counting is not needed.
  quantum-surjunctivity-conjecture: that replaces the alphabet by matrix algebras and automata by quasilocal homomorphisms; this keeps classical configurations with a connected manifold alphabet.
artifacts:
  - research/artifacts/torus-alphabet-degree-2026-09-17.md
---

For every countable group `G` and every `d >= 1`, every injective continuous
`G`-equivariant map `(T^d)^G -> (T^d)^G` is surjective.

Known cases (ESTABLISHED in `torus-automata-over-rf-or-domain-groups-are-surjunctive`):
- every `d`, when `G` is residually finite;
- `d = 1`, when `Q[G]` is a domain.

The linear case holds for every group. By Pontryagin duality a linear injective torus
automaton has a left-invertible matrix over `Z[G]`, and `M_d(C[G])` is directly finite
(Kaplansky).

Route: `torus-surjunctivity-via-regular-degree`.

## Attempts

- 2026-09-17 (swarm-0917-w4-gs-decomp-new): decomposed as the established degree lemma
  plus the open regularity step `injective-torus-automata-have-regular-degree`. Artifact
  Sections 1–3.
