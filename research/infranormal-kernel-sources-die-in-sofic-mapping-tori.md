---
rg: 2
id: infranormal-kernel-sources-die-in-sofic-mapping-tori
kind: claim
title: In a sofic mapping torus of a Kazhdan kernel, a source infranormal in the kernel saturates the kernel only through a necklace of proper normal subgroups
distinct_from:
  sofic-groups-kill-rigid-compression-defects: that is the absolute criterion for compressors inside a Kazhdan group in which the source is infranormal; this applies it with the kernel as that group and then controls the extrinsic compressors of degree not zero, which the criterion does not reach.
  sofic-defect-cores-have-non-kazhdan-compressor-hull: that proves a compressor lying in a Kazhdan group where the source is infranormal gives no defect, so the compressor hull is non-Kazhdan; this lets the compressor stay outside every Kazhdan group and proves the defect it produces cannot fill the kernel unless the kernel splits as a product of proper normal subgroups.
  sofic-groups-kill-rigid-defects-modulo-kazhdan-kernels: that is the open modulo-kernel version of the criterion; this is an established statement about one normal Kazhdan kernel with cyclic quotient.
  torsion-free-sofic-extrinsic-kazhdan-defect-kernel: that is the open construction problem; this is an obstruction that removes every candidate whose source is infranormal in the kernel, except the necklace case.
artifacts:
  - research/infranormal-kernel-sources-die-in-sofic-mapping-tori-proof.md
  - research/sofic-groups-kill-rigid-compression-defects.md
  - research/intrinsic-compression-defect-functoriality-and-saturation.md
---

**ESTABLISHED.** Setting:
- `G` is a countable sofic group, `K` is a normal subgroup with `G/K = Z`, and `s in G` has degree 1.
- `K` is a nontrivial Kazhdan group.
- `L <= K` is a Kazhdan subgroup that is infranormal in `K`, meaning `Comp_K(L)` generates `K`.

Write `N = <<L>>^K`, `A_j = s^j N s^-j` (each `A_j` is normal in `K`) and let `D_G(L)` be the
intrinsic defect (ICD1). Call `u in Comp_G(L)` *strict* when `u N u^-1 != N`.

1. **(IS0) Roots centralize the normal closure.** Let `M <= G` be Kazhdan with `L` infranormal
   in `M`. Then `C_G(L)` centralizes `<<L>>^M`. In particular `C_G(L) = C_G(N)`.
2. **(IS1) Only strict extrinsic compressors count.** If `u in Comp_G(L)` is not strict, then
   every defect generator `[u c u^-1, l]` is trivial. A strict `u` has degree `m != 0`, and then
   `A_m < N` strictly.
3. **(IS2) Forced non-Hopfian quotient.** If `D_G(L) != 1`, then `K/N` is an infinite
   non-Hopfian Kazhdan group. In particular `N != K`, `L` does not normally generate `K`, and `K`
   is not simple. All strict degrees have the same sign.
4. **(IS3) Central translate.** Let `g >= 1` be the gcd of the strict degrees. If `g = 1`, then
   `D_G(L) != K`.
5. **(IS4) Necklace.** In general, when a strict compressor exists (otherwise `D_G(L) = 1`), put `G_g = K <t>` with `t = s^g`, and
   `U = < C_K(A_(Jg)) : J in Z >`. Then `U` is a proper normal subgroup of `K`, normalized by `t`,
   and
   ```text
   D_G(L) <= U . sUs^-1 . s^2Us^-2 ... s^(g-1)Us^-(g-1).
   ```
   So `D_G(L) = K` forces `g >= 2` and `K = U_0 U_1 ... U_(g-1)`, with `U_rho = s^rho U s^-rho`
   proper and normal in `K`, cyclically permuted by `s`.

**Corollary (kill).** `D_G(L) = K` is impossible whenever `L` is Kazhdan and infranormal in `K`
and **`K` is not a product of finitely many proper normal subgroups**. Since `K` is finitely
generated, this is equivalent to `K` having a unique maximal normal subgroup (two distinct
maximal normal subgroups multiply to `K`; a unique one contains every proper normal subgroup, by
Zorn and finite generation). It holds, for example, when `K` is simple.
It is also impossible when the strict degree gcd is 1. None of this uses torsion-freeness,
finite presentation or quotientlessness.

## What this kills

- **(EK1), (SCZ1) with sources infranormal in the kernel.**
  `torsion-free-sofic-extrinsic-kazhdan-defect-kernel` and
  `split-cyclic-kazhdan-defect-exact-mf-radical` need `D_G(L) = K` in the sofic group
  `G = K semidirectProduct Z`. If `L` is infranormal in `K`, the witness must satisfy all of:
  - `K/<<L>>^K` is an infinite non-Hopfian Kazhdan group;
  - `s^m` strictly compresses the normal subgroup `<<L>>^K` for some `m > 0`, and every
    compressor has degree of one sign;
  - `K` is a product of `g >= 2` proper normal subgroups permuted cyclically by `s`.

  Dead cases include:
  - `L = K`;
  - `L` normal in `K`, or of finite index in `K`;
  - `L` normally generating `K`;
  - simple `K`, such as the Titz Mite--Witzel kernels. This is the upgrade of item (H3) of
    `sofic-defect-cores-have-non-kazhdan-compressor-hull`, which needed the compressor inside `K`;
  - more generally, kernels with a unique maximal normal subgroup;
  - any witness whose strict compressor degrees have gcd 1.
- **Invariant.** The normal closure `N = <<L>>^K` together with the semigroup of strict
  compressor degrees.
- **Step where every member dies.**
  - First step, (IS0): the Kun--Thom normalization makes every root centralize `N`, so
    compressors fixing `N` give no defect.
  - Second step, (IS3): the defect lies in `prod_j C_K(A_j)`. Finite generation of `K` plus
    the Frobenius bound on the degree semigroup puts one translate `A_J` in `Z(K)`. Then `N` is
    central, so `L` is central, hence abelian and Kazhdan, hence finite. So `N = L` is finite and
    cannot be strictly compressed.
- **What survives.** Sources `L` that are *not* infranormal in `K`: the compressors of `L` in `K`
  generate a proper, possibly non-Kazhdan, subgroup. Or necklace kernels
  `K = U_0 ... U_(g-1)` with `g >= 2`.
  - In the necklace case, the sibling obstruction
    `compression-defects-need-strict-kernel-centralizer-towers` additionally kills the case where
    `K` is a subgroup of a finite product of KCF or linear groups.

Proof: `infranormal-kernel-sources-die-in-sofic-mapping-tori-proof`.
