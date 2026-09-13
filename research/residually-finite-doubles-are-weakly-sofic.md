---
rg: 2
id: residually-finite-doubles-are-weakly-sofic
kind: claim
title: Doubles of residually finite groups over arbitrary subgroups are weakly sofic, so the Kun--Thom double is weakly sofic and nonsofic
distinct_from:
  weakly-sofic-not-sofic: that separates the classes with the coset wreath W, whose kernel is a lamp group; this gives a second, amalgam-shaped witness, the group double, whose kernel is a free group.
  symmetric-double-weak-mf: that proves the same doubles weak MF, an operator-norm matrix-corona property; this proves them weakly sofic, a property of finite groups with bi-invariant metrics, by a different permanence theorem.
  kt-pair-group-double-is-nonsofic: that is nonsoficity of the Kun--Thom double; this adds that the same group lies in the weakly sofic class.
  kt-double-is-nielsen-semidirect-product: that identifies the fold kernel of the Kun--Thom double with an explicit free group and its affine action; this uses only that the fold kernel of any double is free.
---

**ESTABLISHED.** Let `G` be a residually finite group and `Gamma <= G` an
arbitrary subgroup.

1. The double `D = G *_Gamma G` is weakly sofic.
2. For every residually finite group `K`, the free-lamp amalgam
   `H_K = G *_Gamma (Gamma x K)` is weakly sofic.

**Consequence.** For the Kun--Thom Theorem E pair
`Gamma = EL_r(F_q[x_1..x_d]) < G = EL_r(F_q[x^(+-1)]) rtimes SL_d(Z)`, `G` is
residually finite (`kun-thom-nonsofic-wreath`) and `D` is not sofic
(`kt-pair-group-double-is-nonsofic`). So `D` is a finitely generated weakly
sofic nonsofic group. It is a second witness to `weakly-sofic-not-sofic`, and
its kernel is a free group rather than a lamp group.

**Mechanism.** The fold retraction `D -> G` has a free kernel, and Glebsky's
extension theorem (Rev. Mat. Iberoam. 39 (2023), Theorem 1.1: weakly sofic
normal subgroup with residually finite quotient) applies. The theorem has no
hypothesis on `Gamma`. So any nonsoficity mechanism that detects `D`
(infranormal compression of a Kazhdan pair, as in Kun--Thom Theorem A version
3) produces no obstruction in finite groups with bi-invariant metrics.

**Brief question answered.** Of the three groups in the lane brief, this
decides the Kun--Thom double: it is weakly sofic. The other two coincide.
Khanh's finitely presented simple nonsofic group is the binary Leavitt unit
group itself (`fp-simple-nonsofic-via-leavitt-unit-group`), whose weak soficity
stays open.

**Credit.** The deduction is immediate from Glebsky's theorem plus Bass--Serre
theory. No source states it; the search was bounded to this graph.

Derivation: `residually-finite-doubles-are-weakly-sofic-proof`.
