---
rg: 2
id: abelian-extensions-kill-kcf-compression-defects
kind: claim
title: Over an abelian quotient, compressors centralize the centralizer when compressed images have trivial kernel centralizers, so the compression defect vanishes
distinct_from:
  kazhdan-subgroups-of-cat0-cd-two-have-trivial-centralizers: that kills centralizers of infinite Kazhdan subgroups inside the kernel K itself; this transfers that vanishing to the intrinsic defect of every Kazhdan subgroup in every group containing K normally with abelian quotient, where the centralizer C_G(L) is NOT trivial (it contains the central Z of K x Z) and the defect still dies.
  finite-rank-kernel-forces-abelian-defect-subgroups: that absorbs the defect into a finite-rank kernel and kills it by a finite-dimensional image; this absorbs the compressor-centralizer commutator [s,z] into the kernel through the abelian quotient and kills it by a centralizer hypothesis, with no representation at all.
  relative-defect-iff-surjective-compressor-endomorphisms: that characterizes vanishing of a relative defect in sofic hosts; this is an unconditional group-theoretic vanishing criterion with no approximation hypothesis.
  compression-defect-dies-in-mf-under-mark-stability: that turns a nontrivial defect into non-MF-ness under a stability hypothesis; this proves the defect it would need is trivial on a whole class of extensions.
---

**ESTABLISHED.** Let `K normal G` with `G/K` abelian, and let `L <= K`. Use the intrinsic
compression-centralizer defect

```text
Comp_G(L) = { s in G : s L s^-1 <= L },    G_comp(L) = <Comp_G(L)>,
D_G(L)    = << [g z g^-1, l] : g in G_comp(L), z in C_G(L), l in L >>_G .
```

Assume

```text
C_K(s L s^-1) = 1     for every s in Comp_G(L).                    (AX)
```

Then:

1. `[s,z] = 1` for every `s in Comp_G(L)` and every `z in C_G(L)`; hence `G_comp(L)` centralizes
   `C_G(L)`.
2. `D_G(L) = 1`. The same holds for the Lean core defect `normalClosure {[t c t^-1, iota gamma]}`
   of any `KazhdanCompressionCore` whose image `iota(Gamma)` is `L` (the compressor `t` lies in
   `Comp_G(L)` and `c` in `C_G(L)`).

**Kazhdan-centralizer-free kernels.** Call a group `K` *KCF* if `C_K(Lambda) = 1` for every
nontrivial Kazhdan subgroup `Lambda <= K`. If `K` is torsion-free and KCF, `G/K` is torsion-free
abelian and `L <= G` is Kazhdan, then `L <= K` (its image in `G/K` is a finite subgroup of a
torsion-free group) and every `s L s^-1` is a nontrivial Kazhdan subgroup of `K` when `L != 1`.
So (AX) holds and **`D_G(L) = 1` for every Kazhdan subgroup `L` of every such `G`**, in particular
for `K x Z`, for every mapping torus `K semidirectProduct_phi Z` (any `phi`, of finite or infinite
outer order) and for `K semidirectProduct Z^d`.

**Titz Mite--Witzel kernels are KCF.** Each residual acts freely and cocompactly on a CAT(0)
building of dimension two (`titz-witzel-simple-kazhdan-cat0-lattices-exist`), so
`kazhdan-subgroups-of-cat0-cd-two-have-trivial-centralizers` gives KCF. Hence no torsion-free
abelian extension of a Titz Mite--Witzel kernel carries a nontrivial compression defect of a
Kazhdan subgroup.

## What this kills

- **(SCZ1)/(EK1) on Titz--Witzel kernels.** `split-cyclic-kazhdan-defect-exact-mf-radical` and
  `torsion-free-sofic-extrinsic-kazhdan-defect-kernel` need `D_G(L) = K != 1` in
  `G = K semidirectProduct_phi Z`. For a Titz--Witzel kernel `D_G(L) = 1` for every `phi` and `L`.
  The "genuinely extrinsic" escape of infinite-order outer actions does not help either: (AX)
  does not look at `phi`.
- **The non-MF clause of the Titz--Witzel route.** `normal-kazhdan-defect-non-mf` needs a normal
  Kazhdan subgroup inside `D_G(L)`, and `compression-defect-dies-in-mf-under-mark-stability`
  needs a nontrivial element of `D_G(L)`. Both are vacuous on every torsion-free abelian extension
  of a Titz--Witzel kernel. The finite-normal and finite-order central-mark branches are vacuous
  in torsion-free groups. Stability at an arbitrary `w != 1` of the simple minimally almost
  periodic kernel is equivalent to non-MF-ness of the kernel (every asymptotic homomorphism kills
  `w` iff its corona image is not injective, by simplicity), so it is a restatement, not a
  mechanism. **So no non-MF mechanism established in the graph can prove
  `titz-witzel-exact-kazhdan-mf-radical-over-z`; that clause needs a new mechanism.**
- **Forced biography of any witness of (EK1).** If `K` is torsion-free, `G = K semidirectProduct Z`
  and `D_G(L) = K != 1`, then (AX) fails: there are a compressor `s` and `z in C_G(L)` with
  `w = [s,z] != 1`, and `w` is a nontrivial element of `K` centralizing the infinite Kazhdan
  subgroup `s L s^-1`. So the kernel is **not KCF**. This excludes, besides the Titz--Witzel
  kernels, every torsion-free cocompact CAT(0) group of dimension two and every torsion-free
  Gromov-hyperbolic group (Remark in the proof route).

Proof: `abelian-extensions-kill-kcf-compression-defects-proof`.
