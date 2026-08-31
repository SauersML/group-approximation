---
rg: 2
id: luck-determinant-fixed-tester-proof
kind: route
title: Apply determinant permanence under subgroups and arbitrary colimits
target: luck-determinant-fixed-two-generator-tester
requires:
  - universal-all-group-subgroup-colimit-class-tester
---

Let `D` be the class of groups satisfying Lueck's determinant conjecture.
The two permanence statements needed here are published with exactly the
strength used in the universal tester.

Wolfgang Lueck, *Survey on L2-invariants and 3-manifolds*,
[arXiv:2102.04549](https://arxiv.org/abs/2102.04549), Conjecture 3.10 and
Remark 3.11(2),(4), records:

1. if `H` is isomorphic to a subgroup of `G` and `G in D`, then `H in D`;
2. if `G=colim_i G_i` is a directed colimit, with structure maps explicitly
   not required to be injective, and every `G_i in D`, then `G in D`.

The same closure package is traced there to Schick and to Lueck's
*L2-Invariants*, Section 13.2. For the subgroup statement, one can also see
the mechanism directly: for a matrix over `Z[H]`, Hilbert-module induction
from `H` to `G` preserves the spectral distribution with the normalized
von Neumann trace, hence preserves its Fuglede--Kadison determinant.

Thus `D` satisfies both hypotheses of
[[universal-all-group-subgroup-colimit-class-tester]]. For its fixed
two-generator finitely presented host `U`, that theorem gives

~~~text
U in D  <=>  every group is in D.
~~~

This is precisely the claimed equivalence. No soficity hypothesis is used;
indeed the point is to isolate the conjecture at a single universal group.
QED
