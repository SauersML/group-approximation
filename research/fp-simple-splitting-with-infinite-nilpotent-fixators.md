---
rg: 2
id: fp-simple-splitting-with-infinite-nilpotent-fixators
kind: route
title: Dead - split a simple group over virtually nilpotent edge groups with every finite fixator infinite
target: fp-simple-group-splits-over-amenable-edge-groups
requires: []
---

Take the first test case of the live regime of the target.  Find a finitely
presented infinite simple group acting minimally on a tree with finite
quotient graph, where:

- vertex stabilizers are hyperlinear;
- edge stabilizers are finitely generated and virtually nilpotent, for example
  torsion-free virtually polycyclic or `Z^n`;
- every finite set of vertex stabilizers has infinite intersection, so no
  finite-intersection acylindricity mechanism applies.

The established permanence theorem for amenable-edge graphs of hyperlinear
groups would then make the group hyperlinear.

Dead, invalidated by `nilpotent-edge-simple-tree-action-has-finite-fixator`:
some finite set of vertex stabilizers must intersect finitely.  Otherwise a
fixator of least Hirsch length is commensurated by the whole group, and the
conjugation map into its abstract commensurator is either trivial, forcing an
infinite center, or injective, making the group linear and residually finite.

What survives in the target is not touched by this obstruction:

- virtually nilpotent edge groups in which every pairwise vertex-stabilizer
  intersection is infinite but some larger finite intersection is finite;
- amenable edge groups that are not virtually nilpotent.
