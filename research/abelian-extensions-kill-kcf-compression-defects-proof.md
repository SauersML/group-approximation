---
rg: 2
id: abelian-extensions-kill-kcf-compression-defects-proof
kind: route
title: Push the compressor-centralizer commutator into the kernel through the abelian quotient, then kill it by the centralizer of the compressed image
target: abelian-extensions-kill-kcf-compression-defects
requires:
  - kazhdan-subgroups-of-cat0-cd-two-have-trivial-centralizers
  - titz-witzel-simple-kazhdan-cat0-lattices-exist
---

**Lemma.** Let `K normal G`, `G/K` abelian, `L <= K`, and assume (AX):
`C_K(s L s^-1) = 1` for every `s in Comp_G(L)`. Then every `s in Comp_G(L)` commutes with every
`z in C_G(L)`.

*Proof.* Fix `s` and `z`, and put `w = s z s^-1 z^-1`.

- `w in K`: its image in the abelian group `G/K` is a commutator, hence trivial.
- `w` centralizes `s L s^-1`. Take `l in L`. Since `z` centralizes `L`, the element `s z s^-1`
  centralizes `s L s^-1`. Since `s L s^-1 <= L`, `z` also centralizes `s L s^-1`. So their
  product `w` does.
- So `w in C_K(s L s^-1) = 1` by (AX). `QED`

**Defect vanishes.** The set of elements of `G` commuting with every element of `C_G(L)` is a
subgroup (the centralizer of `C_G(L)`). By the Lemma it contains `Comp_G(L)`, so it contains
`G_comp(L)`. Hence for `g in G_comp(L)`, `z in C_G(L)`, `l in L`: `g z g^-1 = z`, and
`[g z g^-1, l] = [z, l] = 1`. Every generator of `D_G(L)` is trivial, so `D_G(L) = 1`. For a
`KazhdanCompressionCore` with `iota(Gamma) = L`, the compressor satisfies `t L t^-1 <= L`, so
`t in Comp_G(L)`, and `c in C_G(L)`; the same computation kills `[t c t^-1, iota gamma]`. `QED`

**KCF kernels.** Let `K` be torsion-free and KCF, `G/K` torsion-free abelian, `L <= G` Kazhdan.

- The image of `L` in `G/K` is an abelian quotient of a Kazhdan group, hence finite. A finite
  subgroup of a torsion-free group is trivial. So `L <= K`.
- If `L = 1` then `D_G(L) = 1` trivially (every generator is `[.,1]`).
- If `L != 1`, then for `s in Comp_G(L)` the subgroup `s L s^-1 <= L <= K` is isomorphic to `L`,
  hence a nontrivial Kazhdan subgroup of `K`. KCF gives (AX). The Lemma gives `D_G(L) = 1`.

**Titz Mite--Witzel kernels.** By `titz-witzel-simple-kazhdan-cat0-lattices-exist` each residual
`K` is torsion-free and acts freely and cocompactly on a two-dimensional CAT(0) building, with
`cd K <= 2`. A nontrivial subgroup of a torsion-free group is infinite. So
`kazhdan-subgroups-of-cat0-cd-two-have-trivial-centralizers` gives `C_K(Lambda) = 1` for every
nontrivial Kazhdan `Lambda <= K`: `K` is KCF. Apply the previous paragraph. `QED`

**Biography of an (EK1) witness.** If `D_G(L) = K != 1` with `K` torsion-free and `G/K = Z`, then
`L <= K` as above and `L != 1` (else `D_G(L) = 1`). The Lemma's conclusion fails for some `s, z`,
so `w = [s,z]` is a nontrivial element of `C_K(s L s^-1)`, with `s L s^-1` infinite Kazhdan. So `K`
is not KCF.

**Remark (torsion-free hyperbolic kernels are KCF; standard facts, not used above).** An infinite
Kazhdan subgroup `Lambda` of a hyperbolic group is not virtually cyclic (a virtually infinite
cyclic group has a finite-index subgroup with infinite abelianization, and (T) passes to finite
index), so it contains two loxodromic elements `g, h` with disjoint fixed pairs on the Gromov
boundary. An element `z` commuting with both preserves both fixed pairs, so it lies in the finite
intersection `E(g) cap E(h)` of their maximal elementary subgroups, and has finite order.
Torsion-freeness gives `z = 1`.

**Calibration.**

- *Non-abelian quotient.* The step `w in K` is where abelianness of `G/K` is spent. In general
  `[s,z]` need not lie in `K`, and the lemma says nothing.
- *Non-KCF kernel.* In `K = F x Lambda` with `Lambda` Kazhdan and `F` nontrivial, `C_K(Lambda)`
  contains `F`, (AX) fails, and the lemma gives nothing; this is the shape the biography demands.
- *Model check of the Lemma.* In `G = K x Z` with `K` KCF and `L` Kazhdan, `C_G(L) = 1 x Z` is
  central, so `D_G(L) = 1` directly; the lemma is the non-central version of this.
