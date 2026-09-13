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
- **Graph-of-groups containers over a double, and the rope trick with two
  different embeddings: dead over hosts with finite rational `H_2`.**
  Established, unreviewed:
  - `fp2-vertex-graph-of-groups-infinite-h2-edge-kills-fp3`: a finite graph
    of groups with finite rational `H_2` at every vertex and infinite
    rational `H_2` at some edge has infinite rational `H_3`;
  - `twisted-rope-trick-container-is-not-fp3-over-fp2-hosts`: conjugating
    `ι × 1` to `ι' × π` gives infinite rational `H_3` whenever
    `ker(H_2 ι − H_2 ι') ∩ ker H_2 π` is infinite-dimensional, for instance
    when `ι' = ι` or `H_2(P; Q)` is finite-dimensional.
- **Acyclic-host twisted container: dead.** Take the vertex group
  `P_0 × L × G` and conjugate `(ι_0(y), 1, 1)` to `(1, y, π(y))`. It is
  finitely presented, contains `G` and is an integral homology circle, so it
  passes every trivial-coefficient test. It still fails `FP_3` on product
  coefficients: `acyclic-host-twisted-rope-container-is-never-fp3`, an
  instance of `split-edge-hnn-with-non-fp2-edge-is-not-fp3` (unreviewed;
  found independently by lanes z1-01-ffz-fpinf and z1-01-ffz-fp3). The second
  edge map is split by a retraction with finitely presented kernel, so the
  product defect `H_1(L; Π ZL) ≠ 0` of the double survives into `H_2`.
- **What is left for a one-edge rope container `HNN(A; L; f_1, f_2)` over
  the double.** Trivial coefficients: `H_2 f_1 − H_2 f_2` must be essentially
  injective on `ker H_2 π`. Product coefficients: the degree-one map on
  `H_1(L; Π ZK)` must be injective, so neither edge map may be split by a
  retraction with `FP_2` kernel while the other passes through an `FP_2`
  subgroup. A surviving shape must couple the double to vertex data that is
  not `FP_2` on both sides. Finite presentability of such a container then
  needs a new argument.
- **Untried here: S-machine Higman embeddings** (Sapir–Birget–Rips). The
  source names them as the non-rope alternative giving more control over the
  embedding.
