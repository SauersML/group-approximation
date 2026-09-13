---
rg: 2
id: fn-groups-mod-acyclic-normal-subgroups-are-type-fhn-proof
kind: route
title: "Acyclic kernels give FH_n by selecting finitely many n-cells of the K(P,1) cover"
target: fn-groups-mod-acyclic-normal-subgroups-are-type-fhn
requires: []
artifacts:
  - research/artifacts/zp-fpn-fhn-2026-09-13-part1.md
  - research/artifacts/zp-fpn-fhn-2026-09-13-part2.md
---

Complete proof in Theorem E of
`research/artifacts/zp-fpn-fhn-2026-09-13-part2.md`, §5. It uses Lemma S of
part 1, §1.

1. `B = K(Q,1)` with finite `(n−1)`-skeleton. `Z` is the covering with deck
   group `G` corresponding to `P`; it is a `K(P,1)` with `Z/G = B`.
2. `X = Z^{(n−1)}` has `H_i(X) = H_i(P) = 0` for `i ≤ n−2`. So
   `C_{n−1}(X) → ⋯ → C_0(X) → ℤ → 0` is exact except at `C_{n−1}`, with
   finitely generated free terms. By Lemma S and `FP_n`, `H_{n−1}(X)` is
   finitely generated.
3. `H_{n−1}(X) → H_{n−1}(Z) = H_{n−1}(P) = 0`, and `Z` is obtained from `X`
   by attaching cells of dimension `≥ n`. So each generator is a finite
   combination of boundaries of `n`-cells.
4. `Y = X ∪` (finitely many orbits of those `n`-cells) is free, has finitely
   many orbits of cells, and is `(n−1)`-acyclic.

Unreviewed.
