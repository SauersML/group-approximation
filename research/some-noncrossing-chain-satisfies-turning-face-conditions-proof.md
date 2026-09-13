---
rg: 2
id: some-noncrossing-chain-satisfies-turning-face-conditions-proof
kind: route
title: Hand check of an eight-point chain satisfying the turning-face conditions with its dual
target: some-noncrossing-chain-satisfies-turning-face-conditions
requires: []
---

Points `1, ..., 8` on a circle; partitions are written by their non-singleton blocks. Conditions as in
`research/artifacts/zp-braid-cat0-turning-face-reduction-2026-09-13.md`.

**The chain `F = ({18} < {18, 26})`**, ranks `{1, 2}`.

- I: the corank `{3, 4, 5, 6}` contains consecutive integers.
- II: `{18, 26}` has two blocks, so it is not universal.
- III': in the gap `({18, 26}, 1)` take `x = {18, 26, 35}` and `y = {18, 246}`, both noncrossing and strictly between.
  Their join in the full partition lattice is `{18, 246, 35}`, which is crossing (`2 < 3 < 4 < 5`), so
  `f(x) + f(y) = f(x v_P y)` is not the image of a noncrossing partition: `x, y` fail modularity.
- IV: `F'_1 = {8}`, `F'_8 = {1}`, `F'_2 = F'_6 = ∅`, and `F_i = U_8` for `i = 3, 4, 5, 7`, giving
  `F'_3 = {2,4}`, `F'_4 = {3,5}`, `F'_5 = {4,6}`, `F'_7 = {6,8}`. The maximal chain
  `C = ({48} < {48, 57} < {48, 57, 13} < {48, 57, 123} < {48, 567, 123} < {12348, 567})` consists of noncrossing
  partitions of ranks 1–6 (each block nests or lies outside the others). Its first blocks are `C_4 = C_8 = {4,8}`,
  `C_5 = C_7 = {5,7}`, `C_1 = C_3 = {1,3}`, `C_2 = {1,2,3}`, `C_6 = {5,6,7}`. So `C'_1 = C'_3 = C'_4 = C'_5 = C'_7 =
  C'_8 = ∅`, and `F'_i ∩ C'_i = ∅` for every `i`.

**The dual chain `F* = ({167, 2345} < {1234567})`**, ranks `{5, 6}`. The Kreweras complement of `{18, 26}` is
`{167, 2345}` (in-between point `k'` lies between `k` and `k+1`: `1', 6', 7'` and `2', 3', 4', 5'` are separated
by no block), and that of `{18}` is `{1234567}`.

- I: the corank `{1, 2, 3, 4}` contains consecutive integers.
- II: `{167, 2345}` has two blocks.
- III': in the gap `(0, {167, 2345})` take `x = {24}` and `y = {35}`. Their join is `{24, 35}`, crossing, so they fail
  modularity.
- IV: from the lowest partition `{167, 2345}`: `F*'_1 = ∅`, `F*'_6 = {7}`, `F*'_7 = {6}`, `F*'_2 = {3}`,
  `F*'_3 = {2,4}`, `F*'_4 = {3,5}`, `F*'_5 = {4}`; `8` is a singleton throughout, so `F*'_8 = {7,1}`. The maximal chain
  `C = ({38} < {38, 47} < {38, 47, 56} < {38, 47, 56, 12} < {1238, 47, 56} < {1238, 4567})` is noncrossing, with
  `C_3 = C_8 = {3,8}`, `C_4 = C_7 = {4,7}`, `C_5 = C_6 = {5,6}`, `C_1 = C_2 = {1,2}`. Then `C'_2 = {1}`,
  `C'_3 = ∅`, `C'_4 = ∅`, `C'_5 = {6}`, `C'_6 = {5}`, `C'_7 = ∅`, `C'_8 = ∅`, so `F*'_i ∩ C'_i = ∅` for every `i`. ∎
