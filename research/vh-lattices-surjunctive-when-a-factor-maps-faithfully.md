---
rg: 2
id: vh-lattices-surjunctive-when-a-factor-maps-faithfully
kind: claim
title: A lattice in a product of two trees is surjunctive if some map to a surjunctive group is faithful on one factor subgroup
distinct_from:
  graph-folds-over-surjunctive-groups-are-surjunctive: that is the permanence theorem for graphs of groups; this applies it to the two tree splittings of a complete square complex group, whose vertex groups are the vertical and horizontal free subgroups.
  fp-simple-group-splits-over-amenable-edge-groups: that seeks simple groups splitting over amenable edge groups and records that product-of-trees splittings have virtually free stabilizers; this uses those splittings for surjunctivity, through faithful maps on the stabilizers.
  strict-automaton-on-lattice-in-product-of-trees: that asks for a strict automaton on some such lattice; this constrains every host of one, since its surjunctive quotients must kill elements of both factor subgroups.
artifacts:
  - research/artifacts/vh-lattice-table-hosts-2026-09-12.md
  - research/artifacts/gk-vf-nonlinear-verification-2026-09-12.md
---

**ESTABLISHED** by `vh-lattice-factor-faithful-graph-fold-proof`.

Let `X` be a finite complete one-vertex VH complex with vertical letters `V` and
horizontal letters `H`, and `Gamma = pi_1 X`, a torsion-free lattice acting freely and
vertex-transitively on `T_V x T_H`. Write `F_V = <V>` and `F_H = <H>`, free of ranks `|V|`
and `|H|`.

**Theorem.** If some homomorphism `f : Gamma -> G` into a surjunctive group is injective on
`F_V`, or on `F_H`, then `Gamma` is surjunctive.

**Consequences.**
- A strict automaton over `Gamma` forces every homomorphism from `Gamma` into a surjunctive
  group to kill a nontrivial element of `F_V` and a nontrivial element of `F_H`.
- In particular the finite residual `Gamma_0`, the intersection of all finite-index
  subgroups, meets both `F_V` and `F_H` nontrivially, since `Gamma / Gamma_0` is residually
  finite, hence sofic and surjunctive. A non-residually-finite lattice whose finite
  residual avoids one factor subgroup carries no strict automaton.
- For a virtually simple lattice, of Burger–Mozes type, the hypothesis already embeds a
  finite-index simple subgroup in a surjunctive group, so the filter excludes nothing
  there. Those lattices are the hosts that survive it.

Proof: Section 9 of the artifact.
