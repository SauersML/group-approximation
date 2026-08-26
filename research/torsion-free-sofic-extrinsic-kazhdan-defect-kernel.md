---
rg: 2
id: torsion-free-sofic-extrinsic-kazhdan-defect-kernel
kind: claim
title: Construct a sofic non-residually-finite Kazhdan kernel saturated by an extrinsic cyclic defect
distinct_from:
  torsion-free-sofic-singly-generated-kazhdan-defect-core: That stronger route asks for an intrinsic full-radical group before adjoining Z; here the defect need only saturate the kernel after the cyclic action is added.
  defect-saturation-full-mf-radical: That arithmetic quotient has an intrinsic full MF radical and unknown soficity; this asks instead for a sofic kernel whose radical behavior is caused extrinsically by its mapping torus.
  finitely-generated-rf-automorphism-mapping-torus-is-rf: That no-go theorem proves the kernel sought here must be non-residually finite.
  finite-outer-order-mapping-torus-is-virtually-product: That second no-go theorem shows the genuinely extrinsic route also needs an infinite-order outer action unless the kernel is already non-MF.
artifacts:
  - GroupApproximation/Sofic/NormalKazhdanMFRadical.lean
  - GroupApproximation/Sofic/SoficByAmenablePermanence.lean
---

Construct a nontrivial finitely presented, torsion-free, sofic,
non-residually-finite group `K` with property `(T)`, an automorphism
`phi in Aut(K)`, and a finitely generated Kazhdan subgroup

```text
L <= G = K semidirectProduct_phi Z
```

carrying a one-sided compression configuration such that

```text
D_G(L) = K x {0}.                                      (EK1)
```

Preferably, one element normally generates `K` in `K`.

This is strictly weaker than constructing a sofic group `K` with
`Rad_MF(K)=K`.  Indeed `K` may itself be MF: the compression defect in
`(EK1)` is an ambient phenomenon created by the cyclic action, just as an MF
lamp subgroup can become the exact MF radical of a non-MF wreath product.
The lower radical inclusion therefore has to be proved in `G`, not in `K`.

The non-residual-finiteness requirement is forced rather than cosmetic.
Property `(T)` makes `K` finitely generated.  By
`finitely-generated-rf-automorphism-mapping-torus-is-rf`, a residually finite
`K` would make `G` residually finite and hence MF, contradicting `(EK1)`
together with `normal-kazhdan-defect-non-mf`.

## Attempts

1. **Arithmetic linear kernels.**  Ordinary congruence and linear
   property-`(T)` candidates are residually finite.  The mapping-torus
   theorem rules them out even if an appealing automorphism can be written
   down.
2. **Intrinsic arithmetic saturation.**  The existing Hull--Osin quotient
   escapes residual finiteness and saturates one defect, but its soficity is
   unknown.  It remains a valid stronger route through
   `torsion-free-sofic-singly-generated-kazhdan-defect-core`.
3. **Sofic simple envelope.**  The unconditional simple sofic full-radical
   group is not presently known to be torsion-free, finitely presented, or
   Kazhdan, and supplies no controlled automorphism.  It cannot yet satisfy
   `(EK1)`.
4. **Thom's LEF Kazhdan group.**
   `thom-hyperlinear-kazhdan-without-factorization` supplies exactly a sofic,
   non-residually-finite Kazhdan seed, but the concrete group is not finitely
   presented and has a central element of finite order.  Finite presentation
   cannot be added while retaining LEF, since finitely presented LEF groups
   are residually finite.  A useful envelope theorem would have to preserve
   soficity and torsion-freeness without preserving LEF.
5. **Titz--Witzel simple lattices.**
   `titz-witzel-simple-kazhdan-cat0-lattices-exist` supplies the complementary
   package: explicit finite presentation, torsion-freeness, simplicity,
   property `(T)`, non-residual-finiteness and one-element normal generation.
   Their soficity is not known.  Moreover, by
   `finite-outer-order-mapping-torus-is-virtually-product`, an MF instance
   would need an infinite-order class in `Out(K)` for a genuinely extrinsic
   obstruction; a finite-order outer action only gives a virtually direct
   product.
