---
rg: 2
id: compressed-coset-shifts-carry-strict-equivariant-embeddings
kind: claim
title: A simple Kazhdan group has a Bernoulli coset shift with a strict continuous equivariant self-embedding
invalidates: [fg-simple-kazhdan-surjunctive-via-bernoulli-rigidity]
distinct_from:
  subshift-self-embedding-carries-no-surjunctivity-content: that strictly embeds a proper invariant subshift of the full shift over a free group by a linear automaton; this strictly embeds the full coset shift over a transitive set with infinite stabilizers, over a simple Kazhdan group, by pulling back along a compressor.
  full-shift-maps-to-infinite-stabilizer-coset-shifts-are-constant: that shows continuous equivariant maps from the full shift into coset shifts with infinite stabilizers are constant; this shows the coset shift itself admits strict equivariant self-embeddings, so such shifts carry no surjunctivity content.
artifacts:
  - research/artifacts/simple-kazhdan-hosts-2026-09-12.md
---

**General statement.** Let `G` be a group, `H <= G`, and `u in G` with
`u H u^-1` a proper subgroup of `H`. Then:
- `psi(gH) = g u^-1 H` is a well-defined, equivariant, surjective,
  non-injective self-map of `G/H`;
- for every alphabet with at least two letters, `y -> y o psi` is a continuous,
  equivariant, injective, non-surjective self-map of `A^(G/H)`;
- its image consists of the configurations constant on the fibres of `psi`,
  which have size `[u^-1 H u : H]`, so it pushes the Bernoulli measure onto a
  null set. That matches `injective-measure-preserving-ca-is-surjective` on the
  full shift: a strict injection cannot preserve the Bernoulli measure.

**Instance.** Take `G = R^x` with `R = L_(F_2)(1,2)`, `H = V_1` (Thompson's `V`
acting inside the cylinder `[1]`), and `u` the prefix bijection
`00 -> 0, 01 -> 10, 1 -> 11`. Then `u H u^-1 = V_11 < V_1`, and `[G:H]` is
infinite. Everything property (T) and simplicity give a Bernoulli `G`-space
holds for `A^(G/H)`:
- full support;
- ergodic, strongly ergodic and with spectral gap;
- the finite orbits are the constants;
- the ergodic invariant measures form a closed set (Glasner--Weiss);
- a strict embedding is a measure conjugacy onto its image.

So any argument that uses only these properties of Bernoulli dynamics would
also prove every equivariant continuous injection of `A^(G/H)` surjective, which
is false. Surjunctivity of a simple Kazhdan host has to use freeness of the
regular action, i.e. Curtis--Hedlund--Lyndon locality.

The construction also runs over amenable surjunctive groups, for example
`BS(1,2)` with `H = <a>` and `u = t`. Section 3.3 of the artifact.
