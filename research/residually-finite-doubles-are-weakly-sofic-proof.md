---
rg: 2
id: residually-finite-doubles-are-weakly-sofic-proof
kind: route
title: The fold kernel is free or a free product of lamps, so Glebsky's extension theorem applies
target: residually-finite-doubles-are-weakly-sofic
requires: [kun-thom-nonsofic-wreath, kt-pair-group-double-is-nonsofic]
---

## 1. Glebsky's theorem

Glebsky, *Extensions of a residually finite group by a weakly sofic group are
weakly sofic*, Rev. Mat. Iberoam. 39 (2023), no. 3, 1097--1104, quoted from
the published PDF in `weakly-sofic-not-sofic-proof`:

> **Theorem 1.1.** Let `H` be a normal subgroup of a group `K`. If `H` is
> weakly sofic and `G=K/H` is residually finite, then `K` is weakly sofic.

Residually finite groups are weakly sofic: they embed in a direct product of
finite groups, which is clause (3) of Glebsky's Lemma 1.2
(`glebsky-weak-soficity-is-metric-free`) with trivial normal subgroup.

## 2. The double

Let `D = G *_Gamma G`, with vertex copies `G_1, G_2` and edge group `Gamma`.

- **Fold.** The identity maps `G_1 -> G` and `G_2 -> G` agree on `Gamma`. By the
  universal property of the amalgam they define a retraction `r: D -> G`.
  So `D/ker(r) = G`, which is residually finite.
- **Free kernel.** `r` is injective on `G_1` and `G_2`, hence on every conjugate of
  a vertex group. So `ker(r)` meets every vertex stabilizer of the Bass--Serre
  tree trivially and acts freely on the tree. A group acting freely on a tree
  is free (Serre, *Trees*, Chapter I, Section 3; standard, section number not
  re-checked against the book).
- **Conclusion.** A free group is residually finite, hence weakly sofic. By
  Theorem 1.1, `D` is weakly sofic.

For the Kun--Thom pair the kernel is the explicit free group
`F({b_x : x in G/Gamma, x != o})` of `kt-double-is-nielsen-semidirect-product`.
Only freeness is used here.

## 3. The free-lamp amalgam

Let `H_K = G *_Gamma (Gamma x K)` with `K` residually finite, the edge group
included diagonally as `Gamma x 1`.

- **Fold.** The identity on `G` and the projection `Gamma x K -> Gamma` agree on the
  edge group. They define `r: H_K -> G` with `H_K / ker(r) = G`.
- **Stabilizers.** `r` is injective on `G` and on the edge group `Gamma`, and its
  kernel on `Gamma x K` is `1 x K`. So `ker(r)` has trivial edge stabilizers,
  trivial intersection with conjugates of `G`, and meets each conjugate of
  `Gamma x K` in the corresponding conjugate of `K`.
- **Structure.** A group acting on a tree with trivial edge stabilizers is the
  free product of its vertex stabilizers and a free group (the structure theorem
  of Bass--Serre theory: the quotient graph of groups has trivial edge groups, so
  its fundamental group is the free product of the vertex groups with the free
  fundamental group of the quotient graph). So `ker(r)` is a free product of
  conjugates of `K` and a free group.
- **Conclusion.** Free products of residually finite groups are residually finite
  (Gruenberg, Proc. London Math. Soc. 7 (1957); theorem number not re-checked).
  So `ker(r)` is
  weakly sofic, and Theorem 1.1 makes `H_K` weakly sofic.

## 4. The Kun--Thom instance

- `kun-thom-nonsofic-wreath` records Theorem E: `G` is residually finite. So Section 2
  makes the Kun--Thom double weakly sofic.
- `kt-pair-group-double-is-nonsofic` records Theorem A, version 3: the same double
  is not sofic.

Together they give a weakly sofic nonsofic double. The argument uses no property of
`Gamma`: not property (T), not infranormality, and not the coset action.
