---
rg: 2
id: atlas-o8plus-type-a-repeated-collision-collapse-proof
kind: route
title: Eliminate the dimension-12 orthogonal-natural multiplicity algebra
target: atlas-o8plus-type-a-repeated-collision-collapse
requires:
  - atlas-o8plus-canonical-moved-module-completion-fails
artifacts:
  - experiments/atlas_a4_q1920_o8p_discovery.g
  - experiments/atlas_a4_repeated_module_collision.g
  - research/artifacts/atlas-a4-o8plus-type-a-repeated-collision-gbnp.json
---

The orthogonal verifier constructs the unique singular-parabolic Q class,
the two ambient embedding twists, and both exact marked tuples.  The natural
module `H` is Q-indecomposable of dimension eight, with composition-factor
dimensions

```text
1,1,4,1,1.                                             (O8A-3)
```

Exactly one twist in each marking has the invariant characterization
`dim End_A(H)=12`.  Fix a computed basis `E_0,...,E_11` of that algebra.
Every A-central operator on `H^m` is uniquely

```text
C=sum_i E_i tensor X_i,          X_i in M_m(F2).        (O8A-4)
```

Substitute the generic `C_R=sum E_i x_i` over the free associative algebra
`R=F2<x_0,...,x_11>` into `(O8A-2)`.  Because the variables do not commute,
every matrix substitution `x_i -> X_i` is represented, for arbitrary `m`.

GBNP 1.1.0 computes the strong two-sided basis in two stages.  The relations
`C_R^2=I,(C_R T)^3=I` leave exactly two noncommuting parameters.  For marking
one the collision entries reduce modulo that base ideal to

```text
x0, x1, x1+x0;
```

for marking two they reduce to

```text
x0, x6, x6+x0.                                         (O8A-5)
```

In both cases the full strong basis has twelve elements and every coordinate
difference between `C_R` and `I_8` has zero normal form.  Hence `C_R=I_8` in
the universal coefficient algebra, and every multiplicity evaluation has
`C=I`.  This proves the claim.
