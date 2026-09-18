---
rg: 2
id: higman-chain-group-pbh-iff-chain-configuration
kind: claim
title: The chain BS(1,2) *_Z BS(1,2), the common vertex group of Higman's group and of the Baumslag--Gersten group, lies in B_A iff some B_A group has an element conjugate to its square that conjugates an infinite-order element to its square
distinct_from:
  higman-group-satisfies-boone-higman: that is the open question for Higman's group H4; this is an equivalence for its vertex group G_1, which is also the base of the Baumslag--Gersten HNN extension, and so a necessary condition for both.
  baumslag-gersten-splits-over-bs12-edges: that writes BG as an HNN extension of the height-two tower K and gives a type (A) criterion for BG; this is an equivalence for K itself, whose remaining input is local.
  retracts-inherit-proper-power-conjugacy: that shows the common-retract closure cannot be applied to H4's splittings; this replaces it by a one-sided retract theorem that does apply to G_1.
  pbh-amalgams-over-centralizer-separated-edges: that is the general engine; this is its application to G_1, with the realization input from bs12-base-generator-is-a-centralizer-in-b-a.
---

**ESTABLISHED** by `higman-chain-configuration-reduction-proof` (lane proof, not reviewed;
no priority claimed). It inherits the status of the lane-proved nodes it requires.

Let `G_1 = <a, b, c | a^-1 b a = b^2, b^-1 c b = c^2> = BS(a,b) *_<b> BS(b,c)`. Here `b` is
the base generator of the first factor and the stable letter of the second.

- `G_1 <= H4` as a vertex group of `higman-group-splits-as-amalgams-over-free-subgroups`.
- `G_1 ≅ K`, the height-two tower of `baumslag-gersten-splits-over-bs12-edges`, and `K <= BG`.

**Chain configuration.** A triple `(a, b, c)` in a group `M` with `a^-1 b a = b^2`,
`b^-1 c b = c^2` and `c` of infinite order.

## Statement

The following are equivalent.
1. `G_1 ∈ B_A`.
2. Some group in `B_A` contains a chain configuration.
3. Some finitely presented twisted Brin--Thompson group contains a chain configuration.

So a homomorphism of `G_1` into a `B_A` group that keeps `c` of infinite order is already
enough. If `G_1 ∈ B_A`, then `G_1` embeds in a finitely presented simple group.

## Where configurations are and are not

- **Necessary for both test cases.** If `H4 ∈ B_A` or `BG ∈ B_A`, then (2) holds.
- **Not in quasi-linear groups.** In a linear group over any field, `c` has finite order
  in every chain configuration. So configurations avoid every finite product of linear
  groups, and `quasi-linear-groups-satisfy-permutational-boone-higman` cannot supply one.
- **Not in metabelian groups.** `b = [a^-1, b]` and `c = [b^-1, c]` lie in the derived
  subgroup, so they commute when it is abelian, and then `c = c^2`.
- **Not created by closure.** By item 4 of `pbh-amalgams-over-centralizer-separated-edges`,
  the amalgam and identity-edge steps produce a configuration only from one already in
  their input.
- **A canonical candidate.** Let `N` be the normal closure of `c`. Then
  `M_1 = G_1 / [N, N] = (⊕_(A/<b>) Z[1/2]) ⋊ A`, with `A = <a, b> = BS(1,2)` and `b`
  acting on the lamp at the base coset by doubling, contains a configuration. So
  `M_1 ∈ B_A` implies `G_1 ∈ B_A`. `M_1` is finitely generated and solvable of derived
  length 3, and it is not quasi-linear. It is a *twisted* coset lamplighter: its untwisted
  counterpart `Z wr_(A/<b>) A` lies in `B_A` by `bs12-base-generator-is-a-centralizer-in-b-a`.

## Lesson for general BH

For graph-of-groups inputs the whole difficulty is **local and twisted**.
`pbh-amalgams-over-centralizer-separated-edges` makes faithfulness free once a vertex-faithful
image exists. `bs12-base-generator-is-a-centralizer-in-b-a` realizes the edge. What is left
for `G_1`, and so for `H4` and `BG`, is one local configuration: an element `b` with two
personalities, conjugate to its own square and dilating an element of infinite order. The
configuration cannot be linear, metabelian, or produced by the closure theorems. The gap
between `M_1` and `Z wr_(A/<b>) A` is exactly a stabilizer acting on its lamp, and in `G_1`
the element `b` acts on the lamp at the coset `a^n <b>` by `2^(2^n)`, for every `n >= 0`. So
a host must let one element act with unbounded dilation on infinitely many independent
pieces. This is the algebraic face of `h(b) ∈ {0, ∞}`
(`homogeneous-conjugation-invariants-vanish-on-bs-bases`), and it points at
infinite-entropy elements of twisted Brin--Thompson groups, which is where (3) says to look.
