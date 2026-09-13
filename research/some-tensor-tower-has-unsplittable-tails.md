---
rg: 2
id: some-tensor-tower-has-unsplittable-tails
kind: claim
title: Some tower of vector bundles has tails with no soft half splitting, giving a nontrivial hyperfinite W*-bundle
distinct_from:
  tensor-tower-bundle-trivial-iff-tails-softly-split: that is the proved criterion; this is the open existence of a tower that fails it.
  ah-face-bundles-are-trivial: that asserts triviality for all AH face bundles; tensor towers are AH C(X̂)-algebras, so this claim is a special form of its negation.
  toms-no-gamma-algebra-is-trivial-on-closed-bauer-faces: that excludes Toms's doubling towers through their block projections; this asks for a fibred tower with no block structure.
artifacts:
  - research/artifacts/tw-projection-starved-bundle-faces-part2-2026-09-12.md
---

**OPEN.** There are compact metrizable spaces `Y_k` and complex vector bundles
`W_k → Y_k` such that, for some `n` and `ε > 0`, no tail
`U_{n,m} = ⊠_{n<k≤m} W_k` (pulled back to `Π_{k≤m} Y_k`), for any `m > n`, admits a positive
contraction `h` with `tr(h − h²) ≤ ε` and `|tr h − 1/2| ≤ ε` at every point.

By `tensor-tower-bundle-trivial-iff-tails-softly-split`, this is equivalent to the
nontriviality of the R-fibre bundle of `⊗_k End(W_k)` over `Π_k Y_k`. So it would answer
BBSTWW Question 3.14 (`nontrivial-w-star-bundle-with-r-fibres-exists`). It would do so with a
Bauer simplex and a `C(X̂)`-algebra, and no simple algebra would be needed.

## Attempts

- **Split bundles: dead.** If some tail contains `V ⊕ V ⊕ G` with `rank G` small relative
  to `rank V`, then `W_n ⊠ tail` splits with small defect. This covers
  `W_k = θ ⊕ L_k` (Hirshberg–Rørdam–Winter) and the single-projection variant of Toms's
  tower.
- **Small bases: dead.** Suppose `dim Π_{n<k≤m} Y_k ≤ rank U_{n,m}` for some `m`. General
  position gives a trivial half-rank subbundle. So tail dimension must exceed tail rank at
  every depth: superlinear growth, as in Toms's quadratic regime
  (`dim X_i = 2 rank(q_i)²`).
- **Products of spheres with Euler-class bundles: too small.** Rank-`w` bundles over
  `S^{2w}` with `c_w ≠ 0` are indecomposable. But their tensor tails live over bases of
  dimension `Σ 2w_k`, far below `Π w_k`, so they split.
- **Soft versus exact (heuristic, not proved).** Soft half projections in `M_R` retract
  onto Grassmannians `Gr(k, R)`, `|k − R/2| ≤ εR`, glued along partial flags. Gluing
  adjacent Grassmannians kills `H_2`, since `H_2(Fl(k,k+1;R)) → H_2(Gr_k) ⊕ H_2(Gr_{k+1})`
  is an isomorphism. So tautological classes do not obstruct soft splittings. An
  obstruction must use classes of `U` in degrees above about `εR`, or unstable homotopy.
- **Candidate shape (not tested).**
  - `Y_k` Grassmannians or products of projective spaces, with dimension quadratic in the
    rank of the tail.
  - `W_k` indecomposable, for example rank-2 bundles over `CP^{j}` with `c_1² − 4c_2` not a
    square.
  - The tool would be a robust Thom–Porteous argument in Toms's style
    (arXiv:2606.12188v2, Section 6). Such arguments survive 2-norm approximation: every
    soft splitting would have to force a degeneracy of positive normalized rank somewhere.
  - Not attempted beyond this design.
