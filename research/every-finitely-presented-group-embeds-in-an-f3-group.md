---
rg: 2
id: every-finitely-presented-group-embeds-in-an-f3-group
kind: claim
title: "Every finitely presented group embeds in a group of type F_3"
distinct_from:
  every-type-fn-group-embeds-in-a-type-fn-plus-1-group: that asks for an F_{n+1} host for every group of type F_n and every n >= 2; this is only its case n = 2
  every-finitely-presented-group-embeds-in-an-f-infinity-group: that asks for F_infinity hosts and implies this claim; this only asks for F_3 hosts
  universal-fp-group-embeds-in-an-rp-fp3-group: that asks for one recursively presented homological host of a universal group; this is the homotopical statement about all finitely presented groups, equivalent to it through Theorem A of Fournier-Facio--Zaremsky
---

Every finitely presented group admits an injective homomorphism into a group
of type `F_3`.

This is the case `n = 2` of the first part of Zaremsky Problem 1.1 (root
`zaremsky-1-01-type-fn-groups-embed-in-type-fn-plus-1`): type `F_2` means
finitely presented. It is equivalent to the `F_3` half of Question 1.3 of
Fournier-Facio–Zaremsky, arXiv:2607.21727v1: "Does every finitely generated
recursively presented group embed in a group of type F_3?" One direction holds
because finitely presented groups are recursively presented. The other holds
because a finitely generated recursively presented group embeds in a finitely
presented group (Higman 1961).

**Equivalent forms recorded as routes.**

- `universal-fp-group-embeds-in-an-rp-fp3-group` implies this claim through
  Theorem A (`f3-hosts-for-fp-groups-via-universal-rp-fp3-host`).
- This claim implies that one
  (`universal-rp-fp3-host-from-f3-hosts-for-fp-groups`).
- `every-type-fn-group-embeds-in-a-type-fn-plus-1-group` implies this claim
  (`f3-hosts-for-fp-groups-from-type-fn-plus-1-hosts`).
- If this claim fails, a finitely presented group of type `F_2` has no `F_3`
  host, which is `some-type-fn-group-embeds-in-no-type-fn-plus-1-group` with
  `n = 2`.

**Model test.** If some universal finitely presented group `U` were of type
`FP_3`, it would be of type `F_3` (Lemma 2.1 of the source), and `U` itself
would be a host for every finitely presented group. No universal finitely
presented group is known to be of type `FP_3`, which is consistent with the
claim being open.

## Attempts

- **Higman's rope trick: dead.** Fournier-Facio–Zaremsky Theorem B
  (`higman-rope-trick-group-is-never-fp3`): for infinite `G = F/R` with
  `R ≠ 1`, `H_3(Hig_ι(G); Q)` is infinite-dimensional for every finitely
  generated host `P` of the double.
- **Rope trick with two different embeddings, and one-step graph-of-groups
  containers: dead over hosts with finite rational `H_2`.** Lane
  z1-01-ffz-fp3 proves two things. Any finite graph of groups whose vertex
  groups have finite-dimensional `H_2(-; Q)`, and some edge group has
  infinite-dimensional `H_2(-; Q)`, has infinite-dimensional `H_3(-; Q)`. And
  conjugating `ι × 1` to `ι' × π` for two different embeddings `ι, ι'` of the
  double does not help when `H_2(P; Q)` is finite-dimensional. Proof nodes
  land next.
- **Live: an acyclic-host twisted container.** Take the vertex group
  `P_0 × L × G`, with `P_0` finitely presented and acyclic and containing the
  double `L`. Conjugate `y ↦ (ι_0(y), 1, 1)` to `y ↦ (1, y, π(y))`. The result
  is finitely presented, contains `G`, and has the rational homology of a
  circle when `G` is acyclic, so every trivial-coefficient Mayer–Vietoris
  obstruction vanishes. Whether it is of type `FP_3` is open (Bieri–Eckmann
  test with product coefficients). Node lands next.
- **Untried here: S-machine Higman embeddings** (Sapir–Birget–Rips). The
  source names them as the non-rope alternative giving more control over the
  embedding.
