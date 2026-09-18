---
rg: 2
id: small-cancellation-groups-realize-every-wp-complexity
kind: claim
title: Two-generator classical C'(1/6) groups with solvable word problem realize every recursive word-problem complexity, so no single decidable group contains them all
distinct_from:
  complexity-bounded-host-classes-are-not-universal: that proves the general principle with some two-generated decidable excluded input; this shows the excluded inputs can all be taken inside one explicit family of torsion-free two-generator classical C'(1/6) groups, which is what the small-cancellation test case needs.
  uniform-wp-bound-excludes-bh-universal-targets: that uses a finitely presented residually finite input through Kharlampovich--Myasnikov--Sapir; this uses infinitely presented classical small cancellation inputs and elementary Dehn/Greendlinger arguments.
---

**ESTABLISHED (lane proof, not reviewed; classical techniques, no priority claimed).**
Proof route: `classical-small-cancellation-complexity-realization-proof`.

## Statement

Put `c_n = 200*4^n` and, over the alphabet `{a,b}`,

    r_n = a b^(c_n+1) a b^(c_n+2) ... a b^(c_n+13)          (n >= 0).

For `A ⊆ N` put `G_A = <a, b | r_n (n in A)>`.

1. **Small cancellation.** The whole family `{r_n : n >= 0}` satisfies the classical
   `C'(1/6)` condition. So does every subfamily, and each `G_A` is a torsion-free
   `C'(1/6)` group.
2. **Exact detection.** For every `A` and every `n`: `r_n = 1` in `G_A` iff `n in A`.
3. **Decidability.** If `A` is decidable, `G_A` has solvable word problem (Dehn's
   algorithm, using only the relators of length `<= 2|w|`).
4. **Every complexity.** For every recursive `T : N -> N` there is a decidable `A` such
   that no algorithm solves the word problem of `G_A` in time `C*T(C*l) + C*l + C`
   for any constant `C`.
5. **Consequence.** For every finitely generated group `H` with solvable word problem,
   in particular every finitely presented simple group, some `G_A` with `A` decidable
   does not embed in `H`. The same holds for every class of groups sharing one
   recursive word-problem time bound (`complexity-bounded-host-classes-are-not-universal`).

## Why it matters for Boone--Higman

The `G_A` are the tamest infinitely presented inputs one could ask for: two generators,
torsion-free, classical `C'(1/6)`, with a Dehn algorithm. Item 5 shows that even this
family cannot be covered by any one host, and by any host family with a uniform
complexity bound. That includes hyperbolic groups, rational homeomorphism groups
(`rational-homeomorphism-subgroups-have-exponential-wp`), and each individual known
finitely presented simple group. So Boone--Higman for this family already forces the
open `fp-simple-groups-with-arbitrarily-complex-word-problem`. The route is
`complex-fp-simple-groups-via-small-cancellation-bh`, and the test-case node is
`graphical-small-cancellation-inputs-satisfy-boone-higman`.
