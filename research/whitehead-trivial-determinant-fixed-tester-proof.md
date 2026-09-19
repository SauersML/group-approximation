---
rg: 2
id: whitehead-trivial-determinant-fixed-tester-proof
kind: route
title: Apply Schick's direct-limit and subgroup stability theorem
target: whitehead-trivial-fuglede-kadison-fixed-two-generator-tester
requires:
  - universal-all-group-subgroup-colimit-class-tester
  - luck-determinant-fixed-two-generator-tester
---

Let `W` be the class of groups for which the Fuglede--Kadison determinant
homomorphism on `Wh(G)` is trivial.

Thomas Schick, *L2-determinant class and approximation of L2-Betti
numbers*, Trans. Amer. Math. Soc. 353 (2001), 3247--3265,
[arXiv:math/9807032](https://arxiv.org/abs/math/9807032), Definition 1.18
and Theorem 1.19, proves that Whitehead-trivial determinant is

1. inherited by subgroups, and
2. stable under direct limits of directed systems of groups.

His Definition 1.17 uses categorical direct limits, with no injectivity
condition on the structure maps. Thus `W` has precisely the two permanence
properties required by
[[universal-all-group-subgroup-colimit-class-tester]]. Applying that theorem
to its fixed host `U` gives the displayed equivalence.

For context, Lueck, *L2-Invariants from the Algebraic Point of View*,
Conjecture 11.14 and Lemma 11.15(i), records the universal conjecture and
shows that Lueck's determinant conjecture implies it. The implication is
not reversed or used in this reduction. QED
