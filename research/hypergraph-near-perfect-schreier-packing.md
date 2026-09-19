---
rg: 2
id: hypergraph-near-perfect-schreier-packing
kind: claim
title: The spherical local-reservoir package admits a coupled near-perfect Schreier packing
---

Given the finite coloured candidate system supplied by
`spherical-near-perfect-local-package`, find partial bijections for the
tested generators whose domains and ranges omit only `o(N)` vertices, such
that every tested multiplication/relator constraint holds on `1-o(1)` of
the roots and every tested nontrivial word moves `1-o(1)` of the roots.

This is deliberately weaker than `hypergraph-absorption-schreier-matching`:
perfect matchings and exact divisibility are not requested.  By
`partial-schreier-completion-preserves-sofic-loss`, this weaker packing
already suffices for a sofic model.

The uncoupled region of the relation hypergraph is now closed more broadly
than an acyclic incidence condition.

- `spherical-single-relation-near-perfect-packing` solves one relation.
- `spherical-one-shared-map-relation-extension` attaches a relation with
  one previously assigned label.
- [[coherent-reselection-reduces-to-private-label-core]] also attaches a
  relation with two previously assigned labels whenever the third label is
  fresh: define the fresh permutation by exact composition or inverse
  composition.  Reversing private-label peeling reduces every table to its
  label-side relation core.
- Fully old closing equations which are formal consequences of the peeled
  basis cost no new matching; bi-invariance of Hamming distance propagates
  the basis defects to them.

Consequently every Tietze-peelable table, including every one-overlap
relation forest and some relation systems with incidence cycles, already has
the required coherent packing.

The remaining content is **core synchronization**.  After redundant
relations are removed and private-label relations are peeled, every surviving
relation uses only labels constrained elsewhere in the core.  There is then
no fresh permutation that can be defined without changing an existing map.
Any nibble, Hall, or weight-preservation theorem used at this stage must
control agreement of these shared permutation copies, not merely preserve
marginal candidate degrees.

Thus merely reusing two maps is not an obstruction.  The first live
obstruction is a nonredundant relation in the nonempty private-label core.
