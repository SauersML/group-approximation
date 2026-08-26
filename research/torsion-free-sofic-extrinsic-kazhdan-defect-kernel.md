---
rg: 2
id: torsion-free-sofic-extrinsic-kazhdan-defect-kernel
kind: claim
title: Construct a sofic non-residually-finite Kazhdan kernel saturated by an extrinsic cyclic defect
distinct_from:
  torsion-free-sofic-singly-generated-kazhdan-defect-core: That stronger route asks for an intrinsic full-radical group before adjoining Z; here the defect need only saturate the kernel after the cyclic action is added.
  defect-saturation-full-mf-radical: That arithmetic quotient has an intrinsic full MF radical and unknown soficity; this asks instead for a sofic kernel whose radical behavior is caused extrinsically by its mapping torus.
  finitely-generated-rf-automorphism-mapping-torus-is-rf: That no-go theorem proves the kernel sought here must be non-residually finite.
  mapping-torus-mf-radical-lies-in-finite-residual: That sharper no-go proves the kernel sought here can have no nontrivial finite quotient at all.
  finite-outer-order-mapping-torus-is-virtually-product: That second no-go theorem shows the genuinely extrinsic route also needs an infinite-order outer action unless the kernel is already non-MF.
artifacts:
  - GroupApproximation/Sofic/NormalKazhdanMFRadical.lean
  - GroupApproximation/Sofic/SoficByAmenablePermanence.lean
  - research/torsion-free-lef-kazhdan-non-rf-seed.md
---

Construct a nontrivial torsion-free, sofic group `K` with no nontrivial finite
quotient,
with property `(T)`, an automorphism `phi in Aut(K)`, and a finitely
generated Kazhdan subgroup

```text
L <= G = K semidirectProduct_phi Z
```

such that `G` is finitely presented and `L` carries a one-sided compression
configuration with

```text
D_G(L) = K x {0}.                                      (EK1)
```

Preferably, `K` is itself finitely presented and one element normally
generates `K` in `K`.

This is strictly weaker than constructing a sofic group `K` with
`Rad_MF(K)=K`.  Indeed `K` may itself be MF: the compression defect in
`(EK1)` is an ambient phenomenon created by the cyclic action, just as an MF
lamp subgroup can become the exact MF radical of a non-MF wreath product.
The lower radical inclusion therefore has to be proved in `G`, not in `K`.

The absence of finite quotients is forced rather than cosmetic.
Property `(T)` makes `K` finitely generated.  By
`mapping-torus-mf-radical-lies-in-finite-residual`, the MF radical of `G` is
contained in the finite residual of `K`.  Thus `(EK1)` forces that finite
residual to equal `K`, equivalently that every finite quotient of `K` be
trivial.

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
   presented and has a central element of finite order.  The first defect is
   no longer fatal: the target only requires its mapping torus to be finitely
   presented, so a finite automorphic presentation would suffice.  The known
   shift on Thom's concrete quotient is surjective but not injective, however,
   and the central torsion still rules that group out.  A useful variant must
   be torsion-free and carry an actual automorphism whose mapping torus has a
   finite presentation; it need not make `K` finitely presented.
   Passing to finite index cannot remove the torsion: the central element lies
   in the finite residual, so it lies in the kernel of the finite coset action
   associated to every finite-index subgroup and hence belongs to every such
   subgroup.
5. **The de Cornulier--Thom finitely presented variant.**  This repairs finite
   presentation but not the decisive clauses: its soficity is open and its
   centre contains the Prüfer group `Z[1/p]/Z`.  Every map from that divisible
   subgroup to a finite group is trivial, so every finite-index subgroup again
   contains torsion.  Its surjective noninjective dilation is not an
   automorphism and therefore does not define the required split extension.
6. **Titz--Witzel simple lattices.**
   `titz-witzel-simple-kazhdan-cat0-lattices-exist` supplies the complementary
   package: explicit finite presentation, torsion-freeness, simplicity,
   property `(T)`, non-residual-finiteness and one-element normal generation.
   Their soficity is not known.  Moreover, by
   `finite-outer-order-mapping-torus-is-virtually-product`, an MF instance
   would need an infinite-order class in `Out(K)` for a genuinely extrinsic
   obstruction; a finite-order outer action only gives a virtually direct
   product.
7. **Characteristic-zero Thom/Kida--Tucker-Drob seed.**
   `torsion-free-lef-kazhdan-non-rf-seed` now supplies unconditionally all
   four intrinsic kernel properties: finitely generated, torsion-free, LEF
   (hence sofic), non-residually-finite and property `(T)`.  This removes the
   former seed-existence gap, but the sharper finite-residual theorem now
   rules out the entire seed family.  Its characteristic centre has a
   nontrivial finitely generated residually finite linear quotient, so every
   automorphism mapping torus has MF radical contained in that centre.  This
   remains true for companion-matrix refinements and is independent of finite
   presentability or the choice of compression data.
8. **The finite-presentation strengthening is a separate open problem.**
   If this claim is strengthened by requiring `K` itself finitely presented,
   then `K` is a finitely presented sofic Kazhdan non-residually-finite group.
   This is exactly the existence question isolated as Open Problem 6.1 by
   Alekseev--Thom (2026); see
   `fp-kernel-crosses-alekseev-thom-open-problem`.
   The direct route should therefore first retain the infinitely presented
   kernel option and seek finite presentability only for the mapping torus,
   but the kernel must now be finite-residual-full rather than a central
   extension of a visible linear quotient.
