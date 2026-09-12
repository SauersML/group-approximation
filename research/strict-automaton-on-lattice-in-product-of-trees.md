---
rg: 2
id: strict-automaton-on-lattice-in-product-of-trees
kind: claim
title: Some lattice in a product of two trees carries an injective non-surjective cellular automaton
distinct_from:
  leavitt-unit-group-nonsurjunctive: that seeks a strict automaton on the Kazhdan Leavitt unit group; this seeks one on a CAT(0) a-T-menable lattice acting on a product of two trees, a host with no Kazhdan subgroup and decidable normal forms.
  unicyclic-strict-designs-present-nonsofic-one-relator-groups: that concerns table cores with one independent cycle, which are one-relator groups; this concerns square-complex table cores with many relators and flats.
artifacts:
  - research/artifacts/vh-lattice-table-hosts-2026-09-12.md
---

**OPEN.** Exhibit a cocompact lattice `Gamma` in `Aut(T_1) x Aut(T_2)`, a finite
alphabet `A` and a cellular automaton `tau : A^Gamma -> A^Gamma` that is injective
and not surjective.

Such a `tau` refutes `gottschalk-surjunctivity-conjecture`. It also makes `Gamma`
nonsofic. That would be the first nonsofic group with the Haagerup property, found
by a mechanism with no Kazhdan subgroup at all, since
`a-t-menable-groups-have-no-rigid-compression-defect` rules out every rigid
compression defect there.

Only non-residually-finite irreducible lattices can work. Reducible and arithmetic
lattices are residually finite, hence sofic and surjunctive. Burger–Mozes groups are
the flagship candidates; their soficity is recorded as unknown by Cornulier.

## Attempts

* **Approach, and why (gk-free-wild, 2026-09-12).** By
  `strict-automata-live-on-canonical-table-groups` and the holonomy normal form, a
  counterexample is a table presentation. `mixed-bigon-difference-graphs-present-vh-square-complexes`
  shows every one-vertex VH square complex is the table group of an explicit star
  partition. Complete VH complexes are exactly the lattices in products of trees acting
  simply transitively on vertices. They have unique normal forms, so every reverse
  table is decidable. They contain `Z^2`, so they escape
  `cubulated-hyperbolic-table-cores-carry-no-strict-pair`.
* **Realizing the forward table is not the obstacle.**
  `bijective-designs-force-every-finite-presentation` (gk-n-twocycle, 54ab1d134f) forces
  every finite presentation, and so every VH lattice, as the principal forward table of
  a design over `F_2^T`. That design is bijective over every group. A forced square core
  is therefore no evidence on its own. Two things are needed:
  * the rules must force the squares through an irreversible component;
  * some reverse hinge word must survive in the lattice.
* **Where it dies now.**
  * Single-track 0/1 linear rules pair every product, so they never force only the star
    partition.
  * Two-by-two linear track gadgets force 2-torsion (Lemma D of the artifact), and these
    lattices are torsion-free.
  * At the Boolean level, strict data are uniform codes solving the forward network and
    failing the transposed one (`boolean-core-is-uniform-single-demand-network-coding`).
  * Group-realized 2x2 reverse tables are transposes
    (`smallest-boolean-strict-core-is-a-one-sided-inverse`), so the irreversible part needs
    larger shapes.
* **Next.**
  1. Take Wise's non-residually-finite complete square complexes as hosts.
  2. Modify the shift–shear design so the decoder reads a key track at two addresses
     joined by a square, making the encoder non-invertible.
  3. Certify the surviving hinge with the normal form.
