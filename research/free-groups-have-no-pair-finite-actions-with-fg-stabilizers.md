---
rg: 2
id: free-groups-have-no-pair-finite-actions-with-fg-stabilizers
kind: claim
title: A finitely generated subgroup of infinite index in a free group has infinitely many double cosets, so free groups have no pair-finite actions with finitely generated stabilizers
distinct_from:
  type-a-action-gives-boone-higman-for-subgroups: that turns a type (A) action (finitely many orbits on pairs, finitely presented stabilizers) into a finitely presented simple twisted Brin–Thompson group; this shows a finitely generated free group never has such an action on an infinite set.
  fp-simple-highly-transitive-groups-satisfy-pbh: that is BFFHZ Theorem C, about highly transitive finitely presented simple overgroups; this shows the point stabilizers of any highly transitive (indeed any 2-point-finite) action of a free group are infinitely generated.
  v-and-a-homeomorphism-never-generate-a-free-product: that refutes one claimed witness of a dense subgroup with infinitely generated clopen stabilizers; this lemma is the input for the correct witness, `homeo-cantor-has-dense-free-subgroups-without-fg-stabilizers`.
---

**ESTABLISHED** (lane proof, elementary, not reviewed). No novelty claimed; the
double-coset folding argument is standard Stallings-graph technology.

## Statement

Let `F` be a free group of finite rank `r >= 1`.

1. **Lemma.** If `H <= F` is finitely generated and `[F:H] = ∞`, then the double
   coset space `H\F/H` is infinite.
2. **Corollary.** Let `F` act on a set `X`, let `x ∈ X` have infinite orbit, and
   suppose `F` has finitely many orbits on the set of pairs `Fx × Fx`. Then the
   stabilizer `F_x` is not finitely generated.
3. In particular a finitely generated free group has no action of type (A) on an
   infinite set (Zaremsky's type (A): finitely many orbits on 2-element subsets,
   equivalently on ordered pairs, and finitely presented stabilizers of finite
   subsets), and every point stabilizer of a highly transitive (even 2-transitive)
   action of a free group on an infinite set is infinitely generated.

## Proof of the lemma

If `r = 1` then `H = 1` and `H\F/H = F` is infinite. Let `r >= 2`, fix a free basis
`X`, and let `Γ` be the Stallings graph of `H` with basepoint `*`: a finite, connected,
folded `X`-labelled graph whose reduced closed paths at `*` read exactly the reduced
words of `H`. (An edge labelled `x` from `p` to `q` counts as an edge labelled `x^{-1}`
from `q` to `p`.)

- **A missing label.** Since `[F:H] = ∞`, `Γ` is not a covering of the rose, so some
  vertex `v` has no outgoing edge with some label `a ∈ X^{±1}`. (A finite folded graph
  with all `2r` labels at every vertex is a finite cover, and `H` would have finite
  index.)
- **The words.** Let `u` be the label of a shortest path from `*` to `v`; it is a
  reduced word. Its last letter `ℓ`, if any, satisfies `ℓ ≠ a^{-1}`, since the last
  edge gives `v` an outgoing edge labelled `ℓ^{-1}`. Pick `b ∈ X^{±1} − {a, a^{-1}}`.
  For `n >= 1` put `g_n = u a^n b a^{-n} u^{-1}`, which is reduced by the choices of
  `ℓ` and `b`.
- **The double-coset graph.** Take disjoint copies `A`, `B` of `Γ` and join `*_A` to
  `*_B` by a path labelled `g_n`. The group elements read by paths from `*_A` to `*_B`
  are exactly `H g_n H`. Fold the prefix `u` of the joining path into `A`, ending at
  `v_A`, and fold its suffix `u^{-1}` (read backwards from `*_B`) into `B`, ending at
  `v_B`. What remains is a segment `S` from `v_A` to `v_B` labelled `a^n b a^{-n}`.
- **The result is folded.** At `v_A` the segment adds an outgoing `a`-edge, which `A`
  lacks. At `v_B` it adds an outgoing `a`-edge (its last edge `a^{-1}` read backwards),
  which `B` lacks. Interior vertices of `S` have two edges with distinct labels. Folding
  preserves the set of group elements read between the two base vertices, and in a
  folded graph each such element is read by a unique reduced path, whose label is its
  reduced word.
- **Length bound.** `S` is a bridge between `A` and `B`, with interior vertices of
  degree 2, so every reduced path from `*_A` to `*_B` traverses all of `S`. Hence every
  element of `H g_n H` has length at least `2n + 1`, and the shortest one has length
  exactly `2|u| + 2n + 1`. So the double cosets `H g_n H`, `n >= 1`, are pairwise
  distinct. ∎

## Proof of the corollary

Put `H = F_x`. The `H`-orbits on `Fx` correspond bijectively to the double cosets
`H\F/H` (the orbit of `gx` corresponds to `HgH`), and they also correspond to the
`F`-orbits on `{x} × Fx`, hence to a subset of the `F`-orbits on `Fx × Fx`. So
`H\F/H` is finite. Since `Fx` is infinite, `[F:H] = ∞`, and the lemma forbids `H`
from being finitely generated. Item 3 follows, since type (A) and 2-transitivity both
give finitely many orbits on pairs, and finitely presented stabilizers are finitely
generated. ∎

## Remarks

- The same argument applies to a virtually free group `G` acting as in item 2. Take a
  free normal subgroup `F ⊴ G` of finite index. Each `G`-orbit on pairs splits into at
  most `[G:F]` orbits of `F`; the `F`-orbits in `Gx` are conjugate, hence infinite; and
  `F_x = F ∩ G_x` has finite index in `G_x`. So a finitely generated `G_x` would give a
  finitely generated `F_x` of infinite index with finitely many double cosets. So virtually free groups
  have no type (A) actions on infinite sets either.
- It is consistent with BFFHZ: free groups are in the permutational class only through
  overgroups (for example `F_2 ≤ V`), never as their own actors.
