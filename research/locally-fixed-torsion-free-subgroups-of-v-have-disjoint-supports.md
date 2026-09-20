---
rg: 2
id: locally-fixed-torsion-free-subgroups-of-v-have-disjoint-supports
kind: claim
title: A torsion-free f.g. subgroup of V fixing a neighborhood of every point has two nontrivial elements with disjoint supports (compression lemma for Q4.7)
distinct_from:
  one-ended-hyperbolic-subgroups-of-v-are-locally-fixed: that proves the hypothesis (every point interior-fixed) for one-ended hyperbolic groups, and this conclusion when a north–south element exists; this is the general compression statement that would finish Question 4.7.
  cyclic-centralizer-subgroups-of-nv-have-meeting-supports: that says groups with cyclic centralizers have pairwise meeting supports; this says local fixedness forces a disjoint pair, so the two together exclude such groups from V.
artifacts:
  - research/artifacts/gq-bh-scout-bbmz-ranked.md
---

**OPEN.** Stated by bh-scout-bbmz, 09-19.

**(COMP).** Let `Γ ≤ V` be finitely generated and torsion-free, acting on `C = {0,1}^ℕ`. Suppose every point of `C` has
a neighborhood fixed pointwise by some nontrivial element of `Γ`. Then `Γ` has two nontrivial elements with disjoint
supports.

Equivalently, there are `γ ∈ Γ`, a nontrivial `g`, and a clopen `W` with a nontrivial pointwise fixer, such that
`γ(cl supp g) ⊆ W`. This is the "compression".

## What it would give

Combine it with `one-ended-hyperbolic-subgroups-of-v-are-locally-fixed`:
- item 1: one-ended hyperbolic subgroups of `V` are locally fixed everywhere;
- item 2: in a torsion-free group with cyclic centralizers, no two nontrivial supports are disjoint.

So **(COMP) implies that no torsion-free one-ended hyperbolic group embeds in `V`**. By passing to a finite-index
subgroup, the same holds for virtually torsion-free ones.
- In particular, closed hyperbolic surface groups and closed hyperbolic 3-manifold groups are not in `V`.
- That answers BBMZ survey Question 4.7 negatively for surfaces
  (`closed-hyperbolic-surface-groups-embed-in-thompson-v`).

A weaker form is enough for this: (COMP) for torsion-free `Γ` with cyclic centralizers, i.e. such `Γ ≤ V` are never
locally fixed everywhere.

## Known cases

- **`Γ` contains an element with north–south dynamics on `C`.** Proved in
  `one-ended-hyperbolic-subgroups-of-v-are-locally-fixed`, item 2. That argument uses local fixedness only, not
  hyperbolicity.
- **The cover by fixed clopens has two pieces.** If `C = W ∪ W'` with both fixers nontrivial, the fixers have
  disjoint supports.

## Calibration against known subgroups of V

- **Torsion cannot be dropped.** `S_3` embeds in `V` by permuting three cones `A, B, C'` with `C = A ⊔ B ⊔ C'`.
  - Each transposition fixes the third cone pointwise, so every point is interior-fixed.
  - The supports `A∪B`, `B∪C'`, `A∪C'` and `C` pairwise meet.
  - Adding `z` that acts as the same infinite-order `ζ ∈ V` on each cone gives `S_3 × Z`, still with no disjoint
    pair. This is an infinite, virtually cyclic counterexample.
  - So (COMP) must assume torsion-freeness. The Q4.7 application only needs the torsion-free case.
- **Groups with disjoint supports** (`Z²`, `F_n × F_m` (the RAAG subgroups of `V`), `F`, `T`, `V`). The conclusion
  holds for them, so there is no conflict.
- **Free subgroups of V.** In the free case, (COMP) says **no free subgroup of `V` is locally fixed everywhere.**
  Checked on two families:
  - **Schottky ping-pong subgroups.** They contain north–south elements, so by the known case an attractor or a
    repeller is not interior-fixed.
  - **Graph subgroups `⟨(x,1),(y,u)⟩ ≤ F_2 × F_2`.** Here each factor acts topologically freely on its own clopen
    `D_i`. The group is `≅ F_2`, and points of `D_1` are not interior-fixed.
  - No free subgroup of `V` that is locally fixed everywhere is known.
- **The decisive test.** Take `x_AB, x_BC, x_AC ∈ V` with `x_ij` supported in `i ∪ j` and fixing the third cone
  pointwise.
  - Every such group is automatically locally fixed everywhere.
  - So (COMP) predicts it is never torsion-free with cyclic centralizers, e.g. never free on these three generators.
  - Ping-pong provably cannot build a free group here. The ping-pong set of `x_BC` must avoid `Fix(x_AB) ⊇ C'` and
    `Fix(x_AC) ⊇ B`, so it lies in `A`, which `x_BC` fixes.
  - Whether some other construction works is open. A yes refutes (COMP), and then Q4.7 needs one-endedness a second
    time.

## Where a proof must work

After passing to a power, an infinite-order `w ∈ V` splits `C = P ⊔ F`, with `w|_P = id` and flow dynamics on `F`
(recalled, not read at source). This gives two gaps:
- several attractors or repellers, where one nontrivial element must fix neighborhoods of all of them at once;
- `P ≠ ∅`.

The three-cone test above is the model case of both.
