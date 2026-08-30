---
rg: 2
id: stw99-lxxvi-dimension-drop-subalgebra-kills-s6-class
kind: claim
title: One unital dimension-drop block kills the unstable S6 scalar clutching class
distinct_from:
  stw99-lxxvi-unital-z-subalgebra-kills-unstable-scalar-classes: that factors through the K-stable unitary group of the full Jiang-Su algebra; this needs only one finite generalized dimension-drop block.
  stw99-lxxvi-unital-matrix-subalgebra-kills-s6-class: that uses finite stable range through a unital matrix algebra; a prime dimension-drop block is projectionless and contains no such matrix algebra.
artifacts:
  - research/artifacts/stw99-lxxvi-fourth-depth-audit-2026-08-30.md
---

For `p,q>=2`, let

```text
I_(p,q)={f in C([0,1],M_p tensor M_q):
         f(0) in M_p tensor 1_q,
         f(1) in 1_p tensor M_q}
```

be the generalized dimension-drop algebra.  If a unital C*-algebra `D`
contains a unital copy of `I_(p,q)`, then the scalar-extension image of

```text
alpha in pi_5(U(2))=Z/2
```

is zero in

```text
pi_5(U(M_2(D))).                                        (1)
```

Thus a coefficient for the surviving `S^6` clutching witness in Problem
LXXVI can contain no unital generalized dimension-drop block with both
endpoint sizes at least two.

This hypothesis is genuinely weaker than the two previous no-go hypotheses.
For relatively prime `p,q>=2`, the prime block `I_(p,q)` has no nontrivial
projections: a projection has constant rank divisible by both `p` and `q`,
so at level one it is zero or the unit.  Hence it contains no unital `M_k`
for `k>=2`.  Being subhomogeneous, it also contains no unital copy of the
simple infinite-dimensional algebra `Z`.  Nevertheless its unitary
homotopy pullback already kills `alpha`.

This does not assert that purity alone forces a dimension-drop embedding.
It narrows the surviving coefficient problem to pure algebras lacking even
one such finite divisibility block, a strictly earlier obstruction than
Z-stability or central-sequence dimension-drop absorption.
