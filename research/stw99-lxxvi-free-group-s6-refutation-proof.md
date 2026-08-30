---
rg: 2
id: stw99-lxxvi-free-group-s6-refutation-proof
kind: route
title: Use the unital Jiang-Su subalgebra of the reduced free-group algebra
target: stw99-lxxvi-free-group-cannot-be-s6-coefficient
requires:
  - stw99-lxxvi-unital-z-subalgebra-kills-unstable-scalar-classes
---

Thiel--Winter, Proposition 4.2 and Remark 4.3 in
[The generator problem for Z-stable C*-algebras](https://arxiv.org/abs/1201.3879),
prove that `Z` embeds unitally into the reduced group C*-algebra of every
group containing a noncyclic free subgroup.  In particular,

```text
Z -> C*_r(F_2)
```

is a unital embedding.  The class `alpha` is stably zero because its image
from `pi_5(U(2))=Z/2` to the torsion-free stable group
`pi_5(U(infinity))=Z` vanishes.  The required conclusion now follows from
`stw99-lxxvi-unital-z-subalgebra-kills-unstable-scalar-classes`.
