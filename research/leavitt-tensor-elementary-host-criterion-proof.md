---
rg: 2
id: leavitt-tensor-elementary-host-criterion-proof
kind: route
title: Embed the perfect subgroup by Whitehead, take simplicity from root detection and finite presentation from Krstić--McCool and the kernel criterion
target: leavitt-tensor-elementary-host-criterion
requires:
  - perfect-unit-subgroups-embed-in-elementary-groups
  - central-simple-leavitt-tensor-unit-groups-are-simple
  - khanh-acyclicity-and-steinberg-criteria
  - fp-quotient-iff-kernel-finitely-normally-generated
artifacts:
  - research/artifacts/bh-decidable-algebra-hosts-2026-09-12.md
---

Derivation. Notation as in the claim.

1. **`R` is a finitely presented ring.** A tensor product over a field of two
   finitely presented algebras is presented by the union of the generators and
   relations, plus the commutation relations between the two generating sets.
   `L` is finitely presented. Adding `2 = 0` presents `R` as a ring.
2. **`S` sits in `R^x`.** `b |-> b ⊗ 1` is an injective unital homomorphism
   `B -> R`, because tensoring over a field is faithful. So `S <= B^x` maps
   injectively into `R^x`, and its image is still perfect.
3. **`S` sits in `E_n(R)`.** Apply `perfect-unit-subgroups-embed-in-elementary-groups`
   to the image of `S` in `R^x`.
4. **`E_n(R)` is simple.** `central-simple-leavitt-tensor-unit-groups-are-simple`,
   part 1: for central simple `B`, `E_n(B ⊗ L)` is simple for every `n >= 3`,
   and part 1 uses no `K`-theory.
5. **`E_n(R)` is finitely presented.** By Krstić--McCool, as imported in
   `khanh-acyclicity-and-steinberg-criteria` item 6, `St_n(R)` is finitely
   presented for `n >= 4`. The natural map `St_n(R) -> E_n(R)` is onto by
   definition, with kernel `K_(2,n)`. By
   `fp-quotient-iff-kernel-finitely-normally-generated`, the quotient is
   finitely presented exactly when `K_(2,n)` is finitely normally generated,
   which is the hypothesis. `∎`

Neither `K_1(R)` nor the stable `K_2(R)` enters, and the unit group `R^x` is
used only as an intermediate container for `S`.
