---
rg: 2
id: hyperbolic-groups-lie-in-the-permutational-class
kind: claim
title: Full contracting rational similarity groups are type (A) actors, so hyperbolic groups and contracting self-similar groups lie in the permutational Boone--Higman class, and finite direct and graph products of them satisfy Boone--Higman
distinct_from:
  hyperbolic-groups-satisfy-boone-higman: that imports the end result of Belk--Bleak--Matucci--Zaremsky, an embedding in some finitely presented simple group; this reads off from their proof that the intermediate host itself carries a type (A) action, which is the stronger, permanence-friendly conclusion.
  hyperbolic-groups-embed-in-contracting-rsgs: that imports the intermediate embedding into a full contracting rational similarity group; this adds that every such group is a type (A) actor.
  boone-higman-type-a-class-closed-under-finite-extensions: that proves closure of B_A under finite products and finite-index overgroups and records that whether the hyperbolic and contracting envelopes pass through type (A) actors was not checked; this checks it, positively.
  boone-higman-closed-under-finite-direct-products: that is the open product closure of the Boone--Higman class; this settles the special case of products of hyperbolic and contracting self-similar groups, and more generally of any factors that already lie in B_A.
  fp-self-similar-subgroups-satisfy-permutational-boone-higman: that puts subgroups of finitely presented self-similar groups in B_A; this does the same for contracting self-similar groups, which need not be finitely presented, and for hyperbolic groups, which need not be residually finite.
artifacts:
  - research/artifacts/bh-rational-similarity-hosts-2026-09-12.md
---

**ESTABLISHED** by `hyperbolic-groups-in-b-a-proof` (lane proof: a read-off from a literature
proof plus landed closure nodes). Referee a (proof gaps): PASS,
`research/artifacts/gq-referee-a-hyperbolic-groups-lie-in-the-permutational-class.md` (2bdad9399),
nit N1 applied. Citation review pending. No priority claimed; see "Priority" below.

Write `B_A` for the class of groups that embed in a group admitting an action of type (A)
(faithful, finitely presented acting group, finitely generated point stabilizers, finitely
many orbits of two-element subsets), as in
`boone-higman-type-a-class-closed-under-finite-extensions`.

## Statement

1. **Actors.** Every full, contracting rational similarity group (RSG) `G ≤ R_{Γ,E}`, in the
   sense of Belk--Bleak--Matucci--Zaremsky (BBMZ), arXiv:2309.06224, acts with type (A) on the
   `G`-orbit of any rational point of `E`. In fact the action is highly transitive and the
   stabilizer of every finite subset is finitely generated.
2. **Inputs.** Hence the following lie in `B_A`:
   - every hyperbolic group;
   - every contracting self-similar group, and every contracting Röver--Nekrashevych group;
   - every subgroup of a full contracting RSG.
3. **Products.** By the closure properties of `B_A` on main, every group built from groups in
   `B_A` by finite direct products, free products, graph products over finite graphs,
   restricted wreath products over sets with finite point stabilizers, subgroups and
   finite-index overgroups satisfies the Boone--Higman conjecture. In particular:
   - every finite direct product `H_1 × ... × H_k` of hyperbolic groups embeds in a finitely
     presented simple group;
   - every graph product of hyperbolic groups over a finite graph does too;
   - every restricted wreath product `H_1 wr H_2` of hyperbolic groups, and more generally
     `A wr_X H` with `A` hyperbolic and `H` hyperbolic acting on `X` with finite point
     stabilizers, does too (`permutational-boone-higman-closed-under-wreath-products`);
   - so do mixed products with other members of `B_A`, for example `H × Aut(F_n)`,
     `H × GL_m(Z)`, `H × A` for `A` a spherical Artin group, or `H × Z^m`.

## Why it is not a formality

`boone-higman-closed-under-finite-direct-products` is open: two finitely presented simple
groups `S_1`, `S_2` give a finitely presented group `S_1 × S_2`, but no finitely presented
simple group containing it is known in general. Product closure is available only inside
`B_A`. Before this node, main placed hyperbolic groups only in the Boone--Higman class, so even
`H_1 × H_2` for two hyperbolic groups with property (T) that are not known to be linear (such
groups are never cocompactly cubulated) had no finitely presented simple overgroup here.

## Named-problem bearing (BBMZ survey arXiv:2306.16356, Problem 5.3)

- **(11) Automatic groups.** Finite direct products of hyperbolic groups are automatic, and
  graph products of automatic groups are automatic (Hermiller--Meier, J. Algebra 171 (1995);
  not read at source by this lane). So item (11) holds for the subclass of finite direct
  products and graph products of hyperbolic groups. This is a partial result on an open named
  item, not a solution.
- **(10) CAT(0) groups.** A finite direct product of hyperbolic CAT(0) groups is CAT(0), so item
  (10) holds for such products. It adds nothing for factors that are already linear or
  cocompactly cubulated, which were covered before.

## Priority

The type (A) action is exactly the one BBMZ use in the proof of their Proposition 5.1 (label
`prop:contr_to_simple`), where they verify the hypotheses of Zaremsky's oligomorphic criterion.
They do not state the permutational conclusion, and Belk--Fournier-Facio--Hyde--Zaremsky,
arXiv:2503.21882 (TeX l.141), list hyperbolic groups among groups known to satisfy Boone--Higman,
not PBH. The consequence for products is a formal combination of that proof with Zaremsky's
product closure. It may well be known to the authors; no statement of it was found in the
three sources read. A MathSciNet-level search was not done.
