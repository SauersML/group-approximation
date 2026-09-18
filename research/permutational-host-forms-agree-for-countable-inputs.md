---
rg: 2
id: permutational-host-forms-agree-for-countable-inputs
kind: claim
title: The type (A), finitary-alternating and simple-host forms of permutational Boone--Higman agree for every input group, finitely generated or not
distinct_from:
  permutational-boone-higman-iff-finitary-alternating-hosts: that states the type (A) / finitary-alternating equivalence for a finitely generated input and derives the PBH reformulation; this observes that neither finite generation nor a word-problem hypothesis on the input is used, adds the simple-host form and the kernel-removal form, and so applies to countable inputs such as GL_n(Q).
  type-a-action-gives-boone-higman-for-subgroups: that is Zaremsky's Corollary B, the payoff for subgroups of a type (A) actor; this is the equivalence of three descriptions of the class of such subgroups.
  boone-higman-type-a-class-closed-under-finite-extensions: that gives the closure properties of the class B_A; this gives equivalent membership tests for it.
  bh-implies-pbh-iff-fp-simple-groups-satisfy-pbh: that is the universal question whether every finitely presented simple group satisfies PBH; this is a per-input statement and assumes nothing about it.
---

**ESTABLISHED** by `permutational-host-forms-agree-for-countable-inputs-proof`
(hand proof assembling landed nodes, not independently reviewed; no novelty is
claimed, the point is only that the inputs are unrestricted).

## Statement

Let `B_A` be the class of groups that embed in a group admitting an action of
type (A) (`type-a-action-gives-boone-higman-for-subgroups`: faithful, finitely
presented actor, finitely generated point stabilizers, finitely many orbits of
two-element subsets). Let `H` be **any** group. No finite generation and no
word-problem hypothesis is placed on `H`. The following are equivalent.

1. `H ∈ B_A`.
2. `H` embeds in a finitely presented group `Γ` acting faithfully on an
   infinite set `X` with `Alt_fin(X) ≤ Γ`.
3. `H` embeds in a finitely presented simple group `S` that itself lies in
   `B_A`.

Each of them implies that `H` embeds in a finitely presented simple group. A
group satisfying them is countable, since it embeds in a finitely presented
group.

**Kernel removal adds nothing.** Let `G` act on a set `S` with type `[A_2]`
(`G` finitely presented, point stabilizers finitely generated, finitely many
orbits on `S^2`, the action not necessarily faithful). Let `K` be the kernel,
and let `H ≤ G` with `H ∩ K = 1`.
- If `G/K` is finitely presented, then `G/K` acting on `S` is of type (A), and
  `H ∈ B_A`.
- If `G/K` is not finitely presented, then the canonical simple quotient
  `SV_{G/K}` of the finitely presented abstract group `SV_G` is not finitely
  presented (`abstract-btb-simple-quotient-fp-gate`). So this construction
  gives no finitely presented simple envelope for `H`.

Whether the relative form alone suffices is Fournier-Facio--Wu--Zaremsky's
Question 5.9 (see `boone-higman-implies-relative-permutational-bh`). Within
twisted Brin--Thompson envelopes, membership in `B_A` is therefore the weakest
target.

## Consequences

- **Hosts that are already in `B_A`.** Twisted Brin--Thompson groups `SV_G` of
  type (A) actors lie in `B_A` (`twisted-btb-clopen-action-is-type-a`).
  Belk--Fournier-Facio--Hyde--Zaremsky prove that finitely presented twisted
  Brin--Thompson groups are "universal among all finitely presented simple
  groups admitting faithful highly transitive actions" (survey
  arXiv:2306.16356v3, end of §4.4). So every finitely presented simple group
  with a faithful highly transitive action lies in `B_A`. By item 3, a group
  that embeds in any such host is in `B_A`.
  - Their Remark 3.5 lists such hosts (`bh-implies-pbh-iff-fp-simple-groups-satisfy-pbh`),
    including every finitely presented simple group of homeomorphisms of the
    Cantor space that contains the commutator subgroup of some Higman--Thompson
    group.
- **Every countable abelian group lies in `B_A`.** It embeds in `VA`
  (Belk--Hyde--Matucci, survey Theorem 4.11). `VA` is a finitely presented
  simple group of Cantor homeomorphisms that contains `V`, and `V` is its own
  commutator subgroup. In particular `(Q,+)` and `GL_1(Q) = Q^x` lie in `B_A`.
- **No local-to-global step.** Membership of every finitely generated subgroup of
  `H` in `B_A` does not give `H ∈ B_A` by any argument recorded here. The
  equivalences need one host for all of `H`.
