---
rg: 2
id: duplicated-arm-whitehead-hecke-closes-native
kind: route
title: Duplicate the anchored arms and cut their selector Whitehead words by one Hecke atom
target: binary-leavitt-native-two-scale-cross-gram-positive
requires:
  - marked-root-star-carries-three-anchored-cells
  - binary-native-selector-atom-hecke-dichotomy
  - center-chain-character-atom-gives-scalar-gram
---

**INVALIDATED PROPOSAL.**  Duplicate the anchored occurrences of `a_m` and
`b_(m+1)` at fresh root positions.  Either make each native product
`b_(m+1)a_m` a literal cross-commutator root, or use the direct partial-swap
Whitehead word

```text
J_(x_m)=E_ij(x_m)E_ji(y_m)E_ij(x_m),
x_m=b_(m+1)a_m,
```

where `y_m` is the reverse prefix partial inverse.  Transport the duplicates
back to the three anchored Pauli cells by fixed Weyl words.  Finally choose a
finite character atom on roots disjoint from the fresh index window, so both
selector words reduce that atom and have positive Hecke cross-Gram.

The intended conclusion was that duplication separates the selector-product
incidence from the commuting anchored centers, while the common atom removes
the two independent multiplicity reservoirs.  This fails for the reasons in
`duplicate-selector-transports-retain-occurrence-seam`: one common transport
cannot change a commuting cross pair into a noncommuting selector root, two
separate transports introduce precisely the uncontrolled relative holonomy,
and the direct Whitehead alternative authenticates only equal typed corners.
The disjoint Hecke cut then computes the tautological Gram of two full
unitaries rather than the prescribed native selector Gram.
