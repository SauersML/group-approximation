---
rg: 2
id: torsion-free-sofic-quotientless-kazhdan-group-exists
kind: claim
title: An infinite torsion-free sofic Kazhdan group with no nontrivial finite quotient exists; it is a necessary gate of the torsion-free exact-radical goal, and refuting it produces a nonsofic hyperbolic group
distinct_from:
  torsion-free-sofic-extrinsic-kazhdan-defect-kernel: that asks for the kernel together with an extrinsic cyclic compression defect; this is only the intrinsic clauses, which every witness kernel of the goal is forced to have.
  relation-cover-rational-lifting-over-quotientless-kazhdan: that asks for a specific relation-cover source of such a group and is equivalent to this bare existence by relation-cover-sofic-envelope-forces-trivial-kernel; this is the bare existence statement, with its necessity for the goal and its summit-hard lower bound.
  lef-kazhdan-group-without-finite-quotients-exists: that supplies an LEF (so sofic) quotientless Kazhdan group, but EL_3 over a unital ring has Weyl torsion and elementary matrices of order p; this demands torsion-freeness.
  titz-witzel-kernel-sofic: that is soficity of one specific simple torsion-free Kazhdan lattice, which would witness this; this asks for any witness.
  fp-sofic-kazhdan-group-not-residually-finite: that asks for a finitely presented sofic Kazhdan non-residually-finite group and allows torsion and finite quotients; this drops finite presentation but demands torsion-freeness and no finite quotient at all.
  sofic-hyperbolic-stages-give-quotientless-kazhdan-monster: that is the established dichotomy giving this claim from soficity of torsion-free hyperbolic Kazhdan groups; this is the open existence statement itself.
---

**OPEN.** There is an infinite, finitely generated, torsion-free, sofic group with property (T)
and no nontrivial finite quotient. (SQK)

Finite generation is automatic from (T). A torsion-free nontrivial group is infinite. So the
content is: **sofic + torsion-free + Kazhdan + nontrivial + no finite quotient**. Such a group is
perfect, since its abelianization is finitely generated and has no nontrivial finite quotient.
It is not residually finite and not linear (Malcev).

## 1. Necessity: every route to the goal passes through (SQK)

Let `(G, K)` witness `torsion-free-sofic-exact-mf-radical-over-z`. Then `K` witnesses (SQK):

- `K` is sofic and torsion-free, since both properties pass to subgroups
  (`local-approximation-properties-are-marked-closed`, item 1);
- `K` is nontrivial and Kazhdan, by hypothesis;
- `K` has no nontrivial finite quotient. Write `G = K semidirect Z`. Then
  `mapping-torus-mf-radical-lies-in-finite-residual` gives `K = Rad_MF(G) <= R_fin(K)`.

The three live routes into the goal meet (SQK) earlier, at their own holes.

- **Titz--Witzel.** `titz-witzel-kernel-sofic` implies (SQK). The lattice is infinite, simple,
  torsion-free and Kazhdan (`titz-witzel-simple-kazhdan-cat0-lattices-exist`), and an infinite
  simple group has no nontrivial finite quotient.
- **Defect core.** `torsion-free-sofic-singly-generated-kazhdan-defect-core` implies (SQK).
  `(TFC1)` gives `Rad_MF(K) = K` through `normal-kazhdan-defect-non-mf`. Every finite group is
  MF, so every homomorphism of `K` to a finite group kills `Rad_MF(K) = K`.
- **Extrinsic kernel.** `torsion-free-sofic-extrinsic-kazhdan-defect-kernel` implies (SQK). Its
  kernel is torsion-free, sofic and Kazhdan, and by `mapping-torus-mf-radical-lies-in-finite-residual`
  it is quotientless.

So (SQK) is a common prerequisite that each route can fail at on its own. It is strictly weaker
than the goal: it asks nothing about MF radicals, finite presentation or cyclic actions.

## 2. Lower bound: a refutation of (SQK) is summit-hard

By `sofic-hyperbolic-stages-give-quotientless-kazhdan-monster` (ESTABLISHED), take `Gamma` a
torsion-free cocompact `Sp(n,1)` lattice. Its Olshanskii--Osin--Sapir torsion-free Tarski
monster quotient `Q` is infinite, torsion-free and Kazhdan, with no proper finite-index subgroup,
and `Q` is sofic as soon as its torsion-free hyperbolic stages are. Hence

```text
not (SQK)  ==>  some torsion-free hyperbolic Kazhdan quotient of Gamma is nonsofic
           ==>  nonsofic-hyperbolic-group.
```

**Class killed.** Consider any argument that the goal is false and uses only the intrinsic
properties the goal forces on its kernel: sofic, torsion-free, Kazhdan, no finite quotient. Every
such argument dies at this step. It would prove `not (SQK)`, and so solve the flagship root. A
refutation of the goal must use finite presentation of `G`, the exact MF radical, or the cyclic
action.

## 3. Known sources and where each stops

- **Kazhdan Tarski monster** (`sofic-hyperbolic-stages-give-quotientless-kazhdan-monster`). This
  source is unconditional except for soficity of the torsion-free hyperbolic stages. If those
  stages are residually finite, the monster is a marked limit of residually finite groups, so it
  is LEF and a fortiori sofic.
- **Titz--Witzel lattices** (`titz-witzel-kernel-sofic`). This is open; they are not elementary
  sofic (`titz-witzel-kernel-not-elementary-sofic`).
- **Arithmetic defect-saturated quotient** (`arithmetic-defect-saturated-kazhdan-group-is-sofic`).
  This is open.
- **Characteristic-zero seed** (`torsion-free-lef-kazhdan-non-rf-seed`). This is unconditional
  for torsion-free, LEF, Kazhdan and non-residually-finite, but it has a nontrivial finitely
  generated residually finite linear quotient (by its characteristic centre). So it has finite
  quotients, and quotientlessness is the one
  missing clause.
- **Relation covers of** `EL_3(LC(X,F_q) semidirect Z)`. This source is dead. By
  `relation-cover-sofic-envelope-forces-trivial-kernel` the envelope forces `K = Q`, and `Q` has
  torsion.

## 4. Dead classes for a direct construction

- **Finitely generated linear groups** are dead: they are residually finite (Malcev).
- **Normally elementary groups** are dead: any quotient of `St_n(R)`, `n >= 3`, over a unital
  ring (`steinberg-images-die-in-torsion-free-groups`). This includes every
  Ershov--Jaikin-type `EL_n` source.
- **Congruence, unipotent, radical and filtration certificates of torsion-freeness** are dead,
  since the witness is perfect (`filtered-torsion-certificates-die-on-perfect-kernels`).
- **Residually finite, LEA-by-permanence and marked-limit-of-finite constructions** do not die at
  quotientlessness, because (EKL2) is false. They must still avoid Weyl-type torsion. None
  torsion-free is known.

## Attempts

- **2026-09-19, swarm-0917-w14-w14-titz-last1 (reframing).** Status: OPEN.
  - Isolated (SQK) as the common necessary gate of the goal and of all three live routes (§1).
  - Proved the summit-hard lower bound through the Kazhdan Tarski monster (§2):
    `sofic-hyperbolic-stages-give-quotientless-kazhdan-monster`.
  - The monster is not a goal witness. MF-ness, `Rad_MF` of its mapping tori and finite
    presentation are all unknown. It is not expected to be finitely presented, since it is
    lacunary hyperbolic but not hyperbolic.

- **2026-09-20, swarm-0917-w20-w20-titz-last1 (cohomology-index).** Torsion-killing covers of the
  elementary sources. Dead for this class; (SQK) stays OPEN.
  - **The class.** Obtain a witness `E` as a cover `E ->> Q` of a known LEF quotientless Kazhdan
    group with torsion, such as `Q_0 = EL_3(LC(X,Z) ⋊ Z)`, with a small kernel `N` so that soficity
    might lift. Small means finitely generated residually finite, or finite-rank abelian or nilpotent.
    The class includes central `Z^k`-covers with relative (T) (Euler-class or Deligne type).
  - **Death step** (`quotientless-rf-kernel-covers-are-central`, ESTABLISHED).
    - A quotientless `E` acts trivially on any such `N`, since the image in `Aut(N)` is residually
      finite by Baumslag or Mal'cev. So the cover is central.
    - Schur, via `torsion-free-central-cover-forces-abelian-finite-subgroups`, then forces every finite
      subgroup of `Q` to be abelian, with at most `rk N` generators.
    - Every `EL_n(R)/Z`, `n >= 3`, contains a finite subgroup mapping onto `S_n`.
  - **Survivors.** Kernels with a nontrivial outer action by a quotientless image. They include the
    infinite-rank relation-module kernels, whose envelope soficity already dies by
    `relation-cover-sofic-envelope-forces-trivial-kernel`, and finitely generated kernels with
    non-residually-finite `Aut` and `Out`.
