---
rg: 2
id: countable-simple-fp2-needs-all-three-hypotheses
kind: claim
title: "Any proof that simple FP_2 groups are countably many must use maximality, perfectness and finite presentability jointly: each pair of them admits a continuum of kernels"
distinct_from:
  simple-fp2-countability-iff-scattered-kernel-spaces: that claim reformulates the target as scatteredness of the spaces MP(H) and describes a counterexample; this one is an obstruction, exhibiting an established uncountable witness for each proper subset of the three hypotheses and naming the forced negative consequences of the target on those witnesses
  kazhdan-hyperbolic-continuum-non-fng-maximal-kernels: that supplies one of the three witnesses; this combines three witnesses into a calibration of countability arguments for Problem 1.20
---

For a finitely generated group `H` and a set `𝒩` of normal subgroups of `H`,
consider three hypotheses:

- **(M)** every `N ∈ 𝒩` is maximal (`H/N` simple);
- **(P)** every `N ∈ 𝒩` is perfect;
- **(F)** `H` is finitely presented (equivalently for this purpose, of type
  FP_2).

By `simple-fp2-countability-iff-scattered-kernel-spaces`, the target
`only-countably-many-simple-groups-of-type-fp2` is exactly the statement
**(M)+(P)+(F) ⇒ `𝒩` countable**. Each weakening that drops one hypothesis is
false, by established witnesses:

1. **Drop (M).** Some finitely presented `H` has uncountably many perfect
   normal subgroups, with pairwise non-isomorphic quotients of type FP_2.
2. **Drop (P).** Some finitely presented, torsion-free, word-hyperbolic Kazhdan
   `H` has `2^aleph_0` maximal normal subgroups, with pairwise non-isomorphic
   infinite simple quotients.
3. **Drop (F).** The finitely generated alternating full group
   `A(G_V × (Z ⋉ {0,1}^Z))` has `2^aleph_0` perfect maximal normal subgroups
   `K_Y`, one for each infinite minimal subshift `Y`.

**Obstruction.** A countability argument ends by showing that some invariant
with countably many values is injective on `𝒩`. This covers:

- a finite normal-generation datum;
- an r.e. or co-r.e. index;
- a finitely generated relation-module datum;
- isolation in the Chabauty space;
- a Cantor–Bendixson rank.

If that injectivity step uses only two of (M), (P), (F), it dies on the witness
for the missing third. So the injectivity step has to fail on witness 1, 2 or 3
unless it reads all three hypotheses. Examples of arguments killed this way:

- **Kuznetsov-type and word-problem arguments**, and any argument about maximal
  kernels of finitely presented groups that does not read perfectness, die at
  witness 2. Its quotients are simple and not finitely presented.
- **Relation-module or Bieri–Strebel finiteness arguments** that do not read
  simplicity die at witness 1.
- **Chabauty or Baire isolation arguments** in `MP(H)` that use only finite
  generation of `H` die at witness 3, where `MP(H)` is uncountable.

**Forced consequences of the target on the witnesses.** If
`only-countably-many-simple-groups-of-type-fp2` holds, then:

- (T1) `A(G_V × (Z ⋉ {0,1}^Z))` is not of type FP_2, so in particular it is
  not finitely presented. So `v-times-shift-alternating-group-is-of-type-fp2`
  is false.
- (T2) For every finitely presented `H` (witness 2 included), all but countably
  many maximal normal `M` fail to have `H/M` of type FP_2. By the kernel
  criterion of `simple-fp2-countability-iff-scattered-kernel-spaces`, this
  means: for every finite `F ⊆ M`, the group `M/⟨⟨F⟩⟩` is not perfect.

Conversely, a disproof needs only one finitely presented group with uncountably
many maximal `M` whose quotient `M/⟨⟨F_M⟩⟩` is perfect for some finite `F_M`.
Witness 2 and the Coulon–Fournier-Facio families it is built from are the
natural test bed.

Proof in `countable-simple-fp2-needs-all-three-hypotheses-proof`.
