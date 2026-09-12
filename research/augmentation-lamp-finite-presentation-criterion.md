---
rg: 2
id: augmentation-lamp-finite-presentation-criterion
kind: claim
title: Finite presentation of a 2-transitive augmentation lamp group is equivalent to two actor finiteness conditions
distinct_from:
  sharply-two-transitive-augmentation-lamp-host-audit: that audits one actor and its HS role; this is the general finite-presentation criterion.
---

ESTABLISHED.  Let a group `A` act 2-transitively on an infinite set `X`,
let

```text
L=direct_sum_X C_2,
M=ker(L -> C_2),
W=L rtimes A,
Gamma=M rtimes A.
```

Then

```text
Gamma is finitely presented
iff
A is finitely presented and a point stabilizer A_x is finitely generated.
                                                               (FP1)
```

Indeed, `Gamma` has index two in the full permutational wreath product
`W`, so finite presentability of either group is equivalent to finite
presentability of the other.  Cornulier's finite-presentation theorem for
permutational wreath products says that `C_2 wr_X A` is finitely presented
exactly when:

1. `C_2` and `A` are finitely presented;
2. point stabilizers are finitely generated;
3. the diagonal action on `X^2` has finitely many orbits.

The first condition for `C_2` is automatic, and 2-transitivity makes the
last condition automatic: the diagonal and off-diagonal are the two
orbits.  This proves (FP1).

For an action of characteristic different from two on the involutions of
a sharply 2-transitive group, a point stabilizer is the centralizer of the
corresponding involution.  Consequently the Andre--Guirardel actor can be
used in a finitely presented augmentation-lamp group only after proving
both that their direct-limit actor is finitely presented and that one
involution centralizer is finitely generated.  Neither statement is in
arXiv:2212.06020.

Reference: Y. de Cornulier, *Finitely presented wreath products and double
coset decompositions*, arXiv:math/0509090, Theorem 1.1/2.11.
