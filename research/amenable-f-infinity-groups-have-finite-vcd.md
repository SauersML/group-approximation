---
rg: 2
id: amenable-f-infinity-groups-have-finite-vcd
kind: claim
title: Every amenable group of type F_infinity has a finite-index subgroup of finite cohomological dimension
distinct_from:
  every-f-infinity-amenable-group-is-elementary-amenable: that asks for elementary amenability; this asks only for finite virtual cohomological dimension, which that claim implies but which does not imply it without amenable-f-infinity-groups-of-finite-cd-are-virtually-soluble.
  f-infinity-without-finite-vcd-non-proper-bnsr-inclusion: that is a BNSR statement about arbitrary F_infinity groups of infinite vcd; this says amenable F_infinity groups never have infinite vcd.
  some-rf-torsion-free-f-infinity-group-has-infinite-cd: that is an existence statement for residually finite groups with no amenability hypothesis; this is a nonexistence statement for amenable groups.
---

**OPEN.** Let `G` be an amenable group of type `F_∞`. Then some subgroup
`H ≤ G` of finite index has `cd_Z H < ∞`.

This is the **infinite-dimensional half** of the decomposition
`f-infinity-amenable-ea-via-finite-vcd-and-finite-cd-case`. The target
`every-f-infinity-amenable-group-is-elementary-amenable` holds exactly when this
claim and `amenable-f-infinity-groups-of-finite-cd-are-virtually-soluble` both hold
(`f-infinity-amenable-ea-forces-both-vcd-halves` gives the forward
direction).

## Attempts

- **Cost of a proof: it proves Thompson's F is not amenable.** `F` is of type `F_∞`
  (`thompson-f-is-of-type-f-infinity`) and contains `Z^n` for every `n`
  (`thompson-f-has-infinite-cohomological-dimension`). A finite-index subgroup
  `H ≤ F` meets each `Z^n` in a finite-index subgroup, which is again free abelian
  of rank `n`, so `cd H ≥ n` for every `n`. So `F` has infinite vcd, and this claim
  forces `F` to be non-amenable. Route: `thompson-f-not-amenable-via-finite-vcd-of-amenable-f-infinity`.
  The whole Thompson difficulty of the target sits in this half. The target's other
  half never mentions a group of infinite dimension.
- **Where known candidates sit.** Every candidate counterexample recorded in this
  graph attacks this half, not the finite-cd half.
  - Grigorchuk's finitely presented ascending HNN extension `G~` of the first
    Grigorchuk group (`f-infinity-amenable-non-ea-via-grigorchuk-hnn`) contains an
    infinite 2-group. Any finite-index subgroup of `G~` meets it in a nontrivial
    torsion subgroup, and a group of finite cd is torsion-free. So `G~` has infinite
    vcd, and if `G~` is of type `F_∞` it refutes this claim.
  - Degrijse, arXiv:1609.07635v1 (24 Sep 2016), p. 1, read from the arXiv PDF on
    2026-09-17, verbatim: "as far as we are aware none of the currently known
    examples of amenable but not elementary amenable groups are known to have finite
    cohomological dimension over any field. For example, many Branch groups,
    including Grigorchuk's example, are commensurable to an n-fold direct product of
    themselves for some n ≥ 2 (see [2]). By Corollary 2.3, the cohomological
    dimension of such a non locally-finite group is infinite over any field."
  - Gandini, arXiv:1106.3022v2, Corollary 4.5, verbatim: "Every finitely generated
    regular branch group has infinite rational cohomological dimension." Remark 4.6
    extends this to finitely generated branch groups.
    - Gandini's Theorem 4.1, quoting Dicks–Dunwoody V.5.3, verbatim: "Let G be a
      group and let H be a subgroup of G of finite index. If G is R-torsion-free,
      then cd_R H = cd_R G." Every group is `Q`-torsion-free.
    - So let `P` contain a finitely generated branch group `B`, and let `H ≤ P` have
      finite index. Then `H ∩ B` has finite index in `B`, so
      `cd_Z H ≥ cd_Q(H ∩ B) = cd_Q B = ∞`.
    - Hence every group containing a finitely generated branch group has infinite
      vcd.
  - The torsion-free Basilica route
    (`torsion-free-f-infinity-amenable-non-ea-via-basilica-hnn`) is not covered by
    Gandini's corollary: the Basilica group is weakly branch, not branch. This lane
    did not verify whether it has infinite vcd.
- **Why amenability must be used essentially.** Many groups of type `F_∞` have
  infinite vcd (Thompson `F`, `T`, `V`, which contain `F` and so contain `Z^n` for every `n`). A proof must use amenability
  in a way that `F` would violate, so it is at least as hard as
  `thompson-f-is-not-amenable`. That is the obstruction, not a route.
