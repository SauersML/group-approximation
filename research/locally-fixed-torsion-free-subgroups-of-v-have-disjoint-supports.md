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
  - **Update (09-19, later): the piece-permuting half is settled in favor of (COMP)**
    (`block-permuting-local-fixers-force-disjoint-supports`, lane proof).
    - If the three generators map cones onto cones, as for labeled transpositions (the torsion-free analogue of
      `S_3`), the group is never torsion-free with cyclic centralizers, so never free.
    - The proof is an iterated commutator: `[x_AB^6, x_BC^6]` is the identity on `A` and on `C'`. If it is trivial,
      the common-power trick gives an element supported in `B`. Either way it has disjoint support from `x_AC`.
    - What is left of the test: generators that mix cones, i.e. map some cone onto a clopen set that is not a union of
      cones. For those, the commutator loses its vanishing on the second cone.

## Where a proof must work

After passing to a power, an infinite-order `w ∈ V` splits `C = P ⊔ F`, with `w|_P = id` and flow dynamics on `F`
(recalled, not read at source). This gives two gaps:
- several attractors or repellers, where one nontrivial element must fix neighborhoods of all of them at once;
- `P ≠ ∅`.

The three-cone test above is the model case of both.

## Attempt: refining the partition to reach Lemma B (bh-scout-bbmz, 09-19)

**Local fixedness survives refinement.** A subset of a piece fixed pointwise by `h` is still fixed pointwise by `h`. So
refining the partition keeps the "each piece has a nontrivial pointwise fixer" property, with the same fixers.

**What fails is the permuting hypothesis of Lemma B.** Lemma B needs each fixer to map pieces *onto* pieces, since after
a power it must preserve every piece. Refinement cannot produce that for fixers with contracting dynamics:
- A north–south element `w` preserves no nontrivial clopen set. If `w(W) = W` and `W` contains a neighborhood of the
  attractor, then `W ⊇ w^{-n}(that neighborhood)`, which grows to `C ∖ {r}`, so `W = C`.
- Mapping pieces onto *unions* of pieces is not enough either. The commutator step
  `Fix[f,g] ⊇ (Fix f ∩ g Fix f) ∪ (Fix g ∩ f Fix g)` needs `g(Fix f) ⊇ Fix f`.

**Where each case now stands.**
- Fixers without contraction on the pieces: Lemma B.
- A single north–south element anywhere in `Γ`: the locally-fixed node, item 2.
- The open case is a fixer, after passing to a power, of the form `C = P ⊔ F` with `P` a nonempty identity region, or
  with at least two attractors or repellers on `F`. Conjugating by powers of `w` gives a cover of `C` by `P`,
  neighborhoods of the repellers, and the sets `w^{-n}(A_j)` over the attractors, each piece with a nontrivial pointwise
  fixer. But these fixers still mix the pieces, and no single element is yet known to fix neighborhoods of two
  attractors at once.

**Natural next step.** Find, inside `Γ`, an element with a single attractor and a single repeller, as a product of
elements whose attractor and repeller sets are in general position (in the style of the convergence-group lemma). Or
show that locally fixed torsion-free groups in `V` cannot have one.

## Attempt: germ commutators and a stabilizer criterion (bh-q47-comp, 09-19)

Landed as `fixers-of-attractor-and-repeller-sets-force-disjoint-supports` (lane proof, not reviewed).
- **Criterion (Proposition C), no local fixedness needed.** Take `γ` with normal form `(γ', P, F, A, R)`. If some
  `h ≠ 1` fixes a neighborhood of `R`, and some `f ≠ 1` fixes `P` pointwise and a neighborhood of `A`, then `f` and
  `γ'^n h γ'^{-n}` have disjoint supports for large `n`. The north–south case is `P = ∅` with `A`, `R` singletons.
- **Germ commutators (Lemma S).** Germs of `V` at a point form an abelian group (F2). So
  `[Γ_X, Γ_X]` fixes a neighborhood of every finite `X`, and `[γ', b]` is the identity on `P` when `b(P) = P`.
- **Stabilizer form.** For torsion-free `Γ` with cyclic centralizers, every `γ` has `Γ_R` cyclic or
  `Γ_A ∩ Stab(P) ⊆ C(γ')`, and the same with `A` and `R` swapped.
- **What is left for Q4.7.** The remaining input is (STAB): some `γ` whose repeller set has a non-cyclic pointwise
  stabilizer, and whose attractor set, together with `P`, has a stabilizer element not commuting with `γ'`. Lemma L
  gives the one-point version only.

Lemma B's consequence for (COMP) needs cyclic centralizers, per its review (7ff5a6abf0); that scope is now stated in
`block-permuting-local-fixers-force-disjoint-supports`.

## State note (bh-q47-comp, 09-19, lane stopped)

**(STAB), exact form.** Let `Γ ≤ V` be torsion-free, one-ended and hyperbolic. (STAB) says: some nontrivial `γ ∈ Γ`,
with normal-form power `γ'` and data `(P, F, A, R)`, satisfies
- `Γ_R` (the pointwise stabilizer of the finite set `R`) is not cyclic, and
- some `b ∈ Γ_A` with `b(P) = P` does not commute with `γ'`,

or the same with `A` and `R` swapped. By `fixers-of-attractor-and-repeller-sets-force-disjoint-supports`, (STAB) gives
two disjoint supports, so it answers Q4.7 negatively for such `Γ`.

**Why the one-point case holds.** Every one-point stabilizer `Γ_x` is non-cyclic. The orbit Schreier graph of `x` is
`Γ/Γ_x`, which is a quasi-tree by HSZ Theorem A. `Γ_x ≠ 1`, since otherwise `Γ` is virtually free. `Γ_x` is not
infinite cyclic, by Lemma L.

**First test: finite tuples.** Is the Schreier graph of `Γ` on the orbit of a finite tuple `(x_1, …, x_k)`, under the
diagonal action on `C^k`, still a quasi-tree? Equivalently, does HSZ Theorem A extend to diagonal actions?
- If yes, the one-point argument gives `Γ_X` non-cyclic for every finite `X`.
- Then (STAB) holds for any `γ` with `P = ∅`, and the remaining work is elements with `P ≠ ∅` (the `Stab(P)` clause).
- Calibrate on `F_2 ≤ V` (Schottky), where tuple stabilizers are cyclic or trivial and the Schreier graphs are
  quasi-trees. That is consistent, since free groups aren't one-ended.
