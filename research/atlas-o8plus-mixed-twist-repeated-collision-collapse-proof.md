---
rg: 2
id: atlas-o8plus-mixed-twist-repeated-collision-collapse-proof
kind: route
title: Reduce the mixed twists to the order-48 centralizer and collapse its path algebra
target: atlas-o8plus-mixed-twist-repeated-collision-collapse
requires:
  - atlas-collision-local-presentation-is-s4
  - atlas-o8plus-type-a-repeated-collision-collapse
  - atlas-o8plus-type-b-repeated-collision-collapse
artifacts:
  - experiments/atlas_a4_q1920_o8plus_mixed_twist_inventory.g
  - experiments/atlas_a4_q1920_o8p_discovery.g
  - experiments/atlas_a4_repeated_module_collision.g
  - research/artifacts/atlas-a4-o8plus-mixed-twist-repeated-v4-gbnp.txt
  - research/artifacts/atlas-a4-o8plus-mixed-twist-repeated-v4-gbnp.json
---

Use the lower-degree marked-S4 presentation from
`atlas-collision-local-presentation-is-s4`.  Its linear relation gives

```text
c^s=c^t
 iff s^-1 c s=t^-1 c t
 iff [c,s t^-1]=1.                                      (MIX-1)
```

Since `c` already centralizes `A=<r,u>`, it lies in the centralizer of

```text
L=<A,s t^-1>,                  |L|=48.                   (MIX-2)
```

The exact module inventory gives, for both markings,

```text
dim End_L(H_A)=8,             dim End_L(H_B)=8,
dim End_L(H_A+H_B)=26.                                  (MIX-3)
```

In particular the mixed problem does not split formally: the two directions
of inter-twist Hom space have total dimension `26-8-8=10`.  This explicitly
rules out a false central-idempotent shortcut.

Put `M=H_A+H_B`.  Fix a basis of the full 26-dimensional algebra
`End_L(M)`.  Every L-central operator on `M^m` is uniquely

```text
C=sum_(i=0)^25 E_i tensor X_i,       X_i in M_m(F2).     (MIX-4)
```

Therefore the generic coefficients live in the free associative algebra
`F2<x_0,...,x_25>` and represent every multiplicity without assuming that
the `X_i` commute.  Relation `(MIX-1)` is automatic in this basis.  Substitute
the generic `C` into the two remaining normal-V4 equations

```text
C^2=I,                    C (T^-1 C T)=T^-2 C T^2.       (MIX-5)
```

For the two markings there are respectively 156 and 154 distinct nonzero
entry relations.  GBNP 1.1.0
computes a strong two-sided basis of 26 linear relations, exactly the 26
coordinates of `C-I`; all 26 target normal forms are zero.  Hence `C=I` on
`M^m` for every `m`.

Finally let a solution act on `H_A^a+H_B^b` with unequal multiplicities.
Set `m=max(a,b)` and add missing copies of either Q-module with collision
operator equal to the identity.  The added blocks commute with both `A` and
`s t^-1`, and the identity collision operator satisfies both the original and
normal-V4 relators.  Hence block direct sum preserves both centrality
conditions and every relator.  It gives a solution on `(H_A+H_B)^m`, which
the preceding universal certificate forces to be the identity.  Its original
summand was therefore already the identity, proving the claim.
