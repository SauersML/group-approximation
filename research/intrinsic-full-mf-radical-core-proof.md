---
rg: 2
id: intrinsic-full-mf-radical-core-proof
kind: route
title: Generate the intrinsic core and use functoriality of the MF radical
target: intrinsic-full-mf-radical-core
requires: []
artifacts:
  - GroupApproximation/Sofic/FullMFRadicalCore.lean
---

# Proof

For a group `G`, let

```text
C(G) = join { K ≤ G : Rad_MF(K)=K }.
```

First, `C(G)` is itself full-radical.  Let `rho` be a matrix-corona
representation of `C(G)`.  For every full-radical subgroup `K ≤ G`, compose
`rho` with the inclusion

```text
K --> C(G).
```

The composite is trivial because `Rad_MF(K)=K`.  Hence `ker(rho)` contains
every such `K`, and therefore contains their join `C(G)`.  Thus `rho` is
trivial and

```text
Rad_MF(C(G))=C(G).                                    (1)
```

Second, the inclusion `K --> G` carries `Rad_MF(K)` into `Rad_MF(G)` by
functoriality.  Every subgroup occurring in the join defining `C(G)` is
therefore contained in `Rad_MF(G)`.  Taking the join gives

```text
C(G) ≤ Rad_MF(G).                                     (2)
```

Third, let `f : G --> H`.  The image of a full-radical group under a
surjective homomorphism is full-radical.  Applying this to the canonical
surjection

```text
C(G) --> f(C(G))
```

and using (1) shows that `f(C(G))` is one of the subgroups generating `C(H)`.
Consequently

```text
f(C(G)) ≤ C(H).                                       (3)
```

Taking `f` to be an inner automorphism proves normality; taking an arbitrary
automorphism and its inverse proves characteristicity.

Equation (1), applied with `G` replaced by `C(G)`, gives

```text
C(C(G)) = C(G),                                       (4)
```

where the formal subgroup statement is `fullMFRadicalCore C(G) = top`.

Finally, (2) proves `C(G)=G => Rad_MF(G)=G`.  Conversely, if
`Rad_MF(G)=G`, then the top subgroup of `G` is itself full-radical and occurs
among the generators defining `C(G)`.  Hence

```text
C(G)=G  <=>  Rad_MF(G)=G.                             (5)
```

The Lean proof follows these five steps directly.
