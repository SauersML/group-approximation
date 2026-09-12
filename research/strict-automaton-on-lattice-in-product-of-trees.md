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
  shows every one-vertex VH complex whose squares read `h v^(-1) h' v'^(-1)` in positive
  letters is the table group of an explicit star partition. Complete VH complexes are exactly the lattices in products of trees acting
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
* **Square-read shift–shear designs are dead (gk-free-wild, second round).** The lead
  asked for the shift–shear design with the decoder reading a key track at two
  square-joined addresses. `shear-designs-are-strict-iff-their-key-automaton-is` proves
  that a key-controlled data shear is strict exactly when its key automaton is. A key
  automaton reading each track at two addresses has cyclic memory after a translation,
  so it is bijective. These designs are bijective over every group, so no reverse hinge
  needs computing over Wise's or Burger–Mozes lattices. The squares are forced by the
  data shear, and such forcing never bears on strictness.
* **Star and mixed-bigon partitions are dead.** Their origin cells are private, so
  `private-origin-rows-force-permutation-encoders` makes every forward-sufficient encoder
  a symbol permutation. A live square table needs anchoring cells `(s, 1_M) ~ (s', m')`
  glued back to the origin row.
* **Hinges are cheap on these hosts.** By `transposed-hinges-are-conjugated-commutators`,
  the square identification `(h, v^(-1)) ~ (v', h'^(-1))` keeps a nontrivial transposed hinge
  exactly when the reflected word `h v'^(-1) h' v^(-1)` is not a square (artifact Section 8).
  So the target lives or dies on irreversibility of the encoder, not on the reverse
  table.
* **Host filter.** By `vh-lattices-surjunctive-when-a-factor-maps-faithfully`, every
  surjunctive quotient of a host must kill nontrivial elements of both factor free
  subgroups, so its finite residual meets both. Virtually simple Burger–Mozes lattices
  pass trivially and remain the natural hosts.
* **Next.** A key automaton that mixes its tracks, is strict on its own, and whose left
  inverse forces an anchored square presentation of a virtually simple lattice. In the
  linear case this is a one-sided matrix inverse over `F_2[Gamma]`, a failure of stable
  finiteness (`stable-finiteness-failure-refutes-surjunctivity`), where two-by-two track
  gadgets need 2-torsion (Lemma D of the artifact).
* **Explicit host: Radu's BMW lattice (w3-lattice, 2026-09-12).**
  - `radu-bmw-lattice-nonsurjunctive` names `Gamma_R` of `radu-bmw-lattice-embeds-in-titz-witzel-kernel`,
    an irreducible, not residually finite cocompact lattice in `Aut(T_3) x Aut(T_3)` with 2-torsion and a
    quoted complete square table. It routes here through `radu-bmw-nonsurjunctivity-gives-lattice-target`.
  - Screens on it (`research/artifacts/radu-lattice-strict-automaton-screens-2026-09-12.md`):
    * no output symmetry of any kind (`radu-bmw-lattice-has-no-invariant-output-injective-automata`),
      although the lattice has torsion;
    * any factorization of a strict automaton has a strict factor
      (`strict-composites-have-strict-factors`), whose memory must generate a nonsofic subgroup. So layers
      reading one square, only horizontal letters, or only vertical letters add nothing;
    * letter hinges always transpose, because every letter is an involution.
