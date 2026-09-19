---
rg: 2
id: luck-determinant-fixed-two-generator-tester
kind: claim
title: One two-generator finitely presented group tests Lueck's determinant conjecture for every group
distinct_from:
  strong-atiyah-torsion-free: that asks for integral von Neumann kernel dimensions over a torsion-free group and has no known unrestricted colimit permanence; this asks for the Fuglede--Kadison determinant lower bound over integral group rings.
  kaplansky-torsion-free-direct-stable-master-tester: that tests algebraic one-sided inverses over fields in the torsion-free lane; this tests an analytic determinant inequality over `Z[G]` for all groups.
  universal-all-group-subgroup-colimit-class-tester: that is the property-independent mechanism; this verifies the exact literature permanence hypotheses for Lueck's named conjecture.
---

For a group `G` and a matrix `A in M_(r,s)(Z[G])`, let

~~~text
r_A^(2): l2(G)^r -> l2(G)^s
~~~

be right multiplication. Lueck's determinant conjecture for `G` asserts

~~~text
det_(N(G))(r_A^(2)) >= 1
~~~

for every such finite matrix.

There exists one fixed two-generator finitely presented group `U` such that

~~~text
U satisfies Lueck's determinant conjecture
  <=>
every group satisfies Lueck's determinant conjecture.
~~~

The group `U` is the all-group universal host in
[[universal-all-group-subgroup-colimit-class-tester]] and has
`Tord(U)={2,3,4,...}`. This is an exact reduction, not a proof of the
remaining determinant inequality for `U` or of the global conjecture.

**ESTABLISHED 2026-08-31** by
[[luck-determinant-fixed-tester-proof]].
