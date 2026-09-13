---
rg: 2
id: binary-leavitt-pbh-via-mif-envelope
kind: route
title: The binary Leavitt unit group is its own finitely presented simple MIF envelope, so BFFHZ Theorem C applies
target: binary-leavitt-unit-group-satisfies-pbh
requires:
  - binary-leavitt-unit-group-is-mif
  - fp-simple-highly-transitive-groups-satisfy-pbh
  - leavitt-unit-group-finitely-presented
  - binary-leavitt-unit-group-is-simple
  - simple-envelope-forces-solvable-word-problem
---

Let `U = L_(F_2)(1,2)^×`.

1. **`U` is finitely presented and simple.** By `leavitt-unit-group-finitely-presented`
   and `binary-leavitt-unit-group-is-simple`. In particular `U` is finitely generated.
2. **`U` has solvable word problem.** `U` is a finitely generated subgroup of the
   finitely presented simple group `U`, so `simple-envelope-forces-solvable-word-problem`
   applies.
3. **`U` is MIF.** By `binary-leavitt-unit-group-is-mif`.
4. **Theorem C.** By `fp-simple-highly-transitive-groups-satisfy-pbh`, condition (iv) is
   that `U` embeds in a finitely presented simple group that is MIF. The identity
   `U -> U` witnesses it, so (i) holds: `U` embeds in a group admitting an action of type
   (A).

This route does not use `leavitt-cantor-module-semidirect-product-is-fp` or the affine
criterion, so the claim no longer rests on that finite presentation theorem alone.
BFFHZ Theorem E (`relative-automorphism-of-fp-simple-mif-group-has-type-a-action`) names
an explicit actor: `Aut_U(U * F_2)` acting on `Hom_U(U * F_2, U)`. `U` embeds in it
through `g ↦ (x_1 ↦ x_1 g, x_2 ↦ x_2)`.
