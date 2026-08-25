---
rg: 2
id: intrinsic-full-mf-radical-core-proof
kind: route
title: Generate the intrinsic core and use functoriality of the MF radical
target: intrinsic-full-mf-radical-core
requires: []
artifacts:
  - GroupApproximation/Sofic/FullMFRadicalCore.lean
  - GroupApproximation/Sofic/FullMFRadicalExactness.lean
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

For the quotient statement, let `q : G --> G/C(G)` and suppose
`K ≤ G/C(G)` is full-radical.  Its preimage `P=q^{-1}(K)` fits into an exact
sequence

```text
1 --> C(G) --> P --> K --> 1.
```

Both the kernel and target are full-radical, so closure under extensions makes
`P` full-radical.  Its defining maximality gives `P ≤ C(G)`.  Every element of
`K` has a lift in `P`, hence is trivial.  Therefore

```text
C(G/C(G)) = 1.                                       (5)
```

Functoriality now gives the universal property.  If `f : G --> H` and
`C(H)=1`, then

```text
f(C(G)) ≤ C(H)=1,
```

so `C(G) ≤ ker(f)`.  If also `C(G)=G`, then `f` is trivial.

For uniqueness, suppose `N` is normal, `Rad_MF(N)=N`, and `C(G/N)=1`.
The first condition gives `N ≤ C(G)`.  Applying the universal property to
the quotient map `G --> G/N` gives `C(G) ≤ N`.  Hence `N=C(G)`.

Finally, (2) proves `C(G)=G => Rad_MF(G)=G`.  Conversely, if
`Rad_MF(G)=G`, then the top subgroup of `G` is itself full-radical and occurs
among the generators defining `C(G)`.  Hence

```text
C(G)=G  <=>  Rad_MF(G)=G.                             (6)
```

For exactness, let `f : G --> H` be onto with full-radical kernel, and let
`K ≤ H` be full-radical.  Its preimage `P=f^{-1}(K)` fits into

```text
1 --> ker(f) --> P --> K --> 1.
```

Closure under extensions makes `P` full-radical, hence `P ≤ C(G)`.  Every
element of `K` lifts to `P`, so `K ≤ f(C(G))`.  Functoriality gives the
reverse inclusion and therefore

```text
f(C(G)) = C(H).                                       (7)
```

For a full-radical normal subgroup `N`, apply (7) to `G --> G/N`.  Finally,
if `C(G)=1` and `K ≤ G`, functoriality of the inclusion `K --> G` forces
`C(K)=1`; thus the core-free class is subgroup-closed.  The orthogonality
characterization follows by applying any proposed orthogonality condition to
the canonical core-free quotient `G --> G/C(G)`.

The Lean proof follows these steps directly.
