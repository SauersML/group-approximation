---
rg: 2
id: pbh-closed-under-wreaths-over-decidable-coset-spaces
kind: claim
title: For finitely generated A, G in B_A and H of decidable membership in G, the permutational wreath product A wr_(G/H) G lies in B_A
distinct_from:
  pbh-closed-under-permutational-wreaths-with-infinite-stabilizers: that asserts closure over every countable G-set and is refuted by wreaths-over-undecidable-cosets-have-unsolvable-wp; this adds the necessary decidability hypothesis.
  wreaths-over-clopen-stabilizer-cosets-lie-in-b-a: that proves the case where H contains, with finite index, the stabilizer of a clopen set for some embedding of G in a finitely presented full clopen-transitive Cantor host.
artifacts:
  - research/artifacts/gq-bh-openq-papers-list.md
---

**OPEN.** Let `A` and `G` be finitely generated groups in the permutational class `B_A`, and
let `H ≤ G` be a subgroup whose membership problem is decidable. Then `A ≀_{G/H} G` lies in
`B_A`.

**Why this form.**
- The decidability hypothesis is necessary: without it the conclusion fails
  (`wreaths-over-undecidable-cosets-have-unsolvable-wp`).
- The claim is implied by the permutational Boone–Higman conjecture
  (`permutational-boone-higman-conjecture`). Under the hypotheses, `A ≀_{G/H} G` is finitely
  generated with solvable word problem: decide the top component with the word problem of
  `G`; group the lamp positions `u_i x_0` into cosets with the membership test for `H`; then
  decide each lamp value with the word problem of `A`.
- It is the corrected wreath-product clause of Zaremsky's Question 5.7 (arXiv:2405.18354,
  TeX l.534–536: "What about wreath products?"), in the embedding form.

**Proved cases on main.**
- Finite point stabilizers: `permutational-boone-higman-closed-under-wreath-products`.
- `G` acting on `G/H` with type (A): Attempt 2 of the refuted node, via
  `type-a-actors-closed-under-type-a-lamp-wreaths`.
- `H` containing a clopen stabilizer with finite index inside a finitely presented full
  clopen-transitive host: `wreaths-over-clopen-stabilizer-cosets-lie-in-b-a`. Instances:
  - `lamp-wreaths-over-cyclic-cosets-of-f2-lie-in-b-a` (`F_2/⟨a⟩`);
  - `lamp-wreaths-over-psl2-tree-vertices-lie-in-b-a` (vertices of the 2-adic tree).

**Natural next test.** `F_2/⟨c⟩` for an arbitrary nontrivial `c`, for example `c = [a,b]`.
Is there a ping-pong copy of `F_2` in `V` in which `⟨c⟩` stabilizes a clopen set?
Alternatively, every finitely generated subgroup `H` of `F_2`.
