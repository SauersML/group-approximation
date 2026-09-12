---
rg: 2
id: bh-edge-membership-necessity-proof
kind: route
title: Kuznetsov plus Britton, applied to a Rips kernel
target: bh-embeddability-forces-decidable-edge-membership
requires: [simple-envelope-forces-solvable-word-problem, belegradek-osin-rips-construction, hyperbolic-groups-satisfy-boone-higman, novikov-boone-fp-group-undecidable-word-problem]
---

*(i).* The groups `A*_C` and `A *_C A` are finitely generated. By
`simple-envelope-forces-solvable-word-problem`, a finitely generated subgroup
of a finitely presented simple group has solvable word problem, so the envelope
group and its subgroup `A` do.

For `a in A`, consider `[t,a] = t a t^-1 a^-1` in `A*_C`. If `a in C` it is
trivial. If `a notin C`, the word has one occurrence of `t` and one of `t^-1`,
and the subword `t a t^-1` is not a pinch because `a notin C`. By Britton's
lemma the word is nontrivial. So `a in C` iff `[t,a] = 1`.

In `A *_C A` write `i_1, i_2` for the two vertex embeddings. By the normal form
theorem for amalgamated free products, `i_1(a) = i_2(a)` iff `a in C`.

Each test is a word-problem instance for the envelope group, of length linear
in `|a|`, so membership in `C` is decidable. Britton's lemma and the normal
form theorem are standard: Lyndon--Schupp, *Combinatorial Group Theory*,
Chapter IV, Section 2.

*(ii).* Let `Q` be a finitely presented group with unsolvable word problem
(`novikov-boone-fp-group-undecidable-word-problem`). Apply
`belegradek-osin-rips-construction` with `H = F_2`, a torsion-free
non-elementary hyperbolic group. It gives `1 -> N -> G -> Q -> 1` with `G`
torsion-free hyperbolic and `N` a quotient of `F_2`, hence two-generated. By
`hyperbolic-groups-satisfy-boone-higman`, `G` embeds in a finitely presented
simple group.

Membership in `N` is undecidable. Fix preimages in `G` of the generators of
`Q`; a word `q` is trivial in `Q` iff its lift lies in `N`, so a membership
algorithm for `N` would solve the word problem of `Q`. By (i), neither `G*_N`
nor `G *_N G` embeds in a finitely presented simple group. `∎`
