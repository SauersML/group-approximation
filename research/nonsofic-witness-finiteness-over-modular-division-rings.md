---
rg: 2
id: nonsofic-witness-finiteness-over-modular-division-rings
kind: claim
title: The nonsofic Kun--Thom double and free wreath have stably finite group rings over every division ring of positive characteristic, and the two torsion-free nonsofic witnesses carry the question on their Kazhdan covers
distinct_from:
  kun-thom-wreath-stably-finite: that treats the direct-sum Z/2 wreath over fields through marked-site tensors; this treats the amalgamated double, the free-product wreath and the integer-lamp wreath over division rings through free and free abelian kernels.
  free-kernel-extensions-keep-modular-stable-finiteness: that is the general extension theorem; this applies it to named nonsofic groups on main and records which cores remain.
artifacts:
  - research/artifacts/direct-finiteness-charp-census-2026-09-13.md
---

Let `D` be a division ring of characteristic `p > 0`.

1. **Kun--Thom double.** Take the Theorem E pair `Gamma = EL_r(F_q[x_1..x_d])` and
   `G = EL_r(F_q[x^(+-1)]) x| SL_d(Z)`, `r, d >= 3`. Then `G *_Gamma G` is not sofic, and
   `D[G *_Gamma G]` is stably finite. The same holds for `D[<G, t | [t, Gamma] = 1>]`.
2. **Free wreath over an amenable action.** The nonsofic group `Z wr^*_X H = (*_X Z) x| H` of
   `free-wreath-over-an-amenable-action-can-be-nonsofic` has stably finite `D[Z wr^*_X H]`.
3. **Torsion-free double of dimension at most three.** Let `D_3 = G_OW *_(Gamma_hat) G_OW` be the
   group of `fp-torsion-free-nonsofic-group-of-cd-at-most-three`, where `G_OW` is the
   Ollivier--Wise Kazhdan cover of `R^x`. Then `D[D_3]` is stably finite (resp. directly finite)
   iff `D[G_OW]` is.
4. **Integer-lamp wreath.** Let `W_hat = (directSum_(G_hat/Gamma_hat) Z) x| G_hat` be the group of
   `integer-lamp-leavitt-cover-wreath-is-torsion-free-nonsofic`. Then `D[W_hat]` is stably finite
   (resp. directly finite) iff `D[G_hat]` is, where `G_hat` is a subgroup of the torsion-free
   hyperbolic Kazhdan cover of `R^x`.

So items 1 and 2 are nonsofic groups on which Kaplansky's stable finiteness holds over division
rings of positive characteristic. Over fields of characteristic zero, Kaplansky's theorem gives
every group. For the torsion-free nonsofic witnesses of items 3 and 4, the question is exactly the
same question for torsion-free Kazhdan covers of the binary Leavitt unit group, whose soficity is
not known.

Proof: `nonsofic-witness-modular-finiteness-proof`. Not independently reviewed.
