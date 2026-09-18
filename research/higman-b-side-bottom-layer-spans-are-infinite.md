---
rg: 2
id: higman-b-side-bottom-layer-spans-are-infinite
kind: claim
title: For derived length at least 3 the b-side relations do not bound the c-span of any element of the bottom derived layer of <a,c> outside P^(k-1), including the second-level candidate [z, z^alpha]
distinct_from:
  higman-b-side-derived-closure-stays-in-bottom-layer: that makes the top A/A^(k-1) free solvable and leaves the bottom layer open; this closes the bottom layer for every element outside P^(k-1), so a one-sided bound fails in every layer.
  higman-one-sided-span-bound-fails-at-derived-length-three: that shows infinite gamma-span for z in A'/A'' in one explicit group; this shows infinite gamma-span in A''/A''' in the universal b-side group, for [z, z^alpha] and for every element of F'' outside P''.
artifacts:
  - experiments/higman-derived-length-three-2026-09-17/bottom_layer_fox.py
  - experiments/higman-derived-length-three-2026-09-17/bottom_layer_fox-output.txt
---

**ESTABLISHED** by `higman-b-side-bottom-layer-spans-proof` (obstruction).

**Statement.** Fix `k >= 3` and let `Q_k = G_b / ncl(F^(k))`, with the notation of
`higman-b-side-derived-closure-stays-in-bottom-layer`: `G_b = <a,b,c | b^a = b^2, c^b = c^2>`,
`F = <a,c>`, `P = ncl_F(c)`. Let `A` be the image of `F`, and put `V_k = A^(k-1)/A^(k) ⊗ Q =
A^(k-1) ⊗ Q`. For every `m >= 1` and every `w in F^(k-1)` with `w ∉ P^(k-1)`, the span of the image of
`w` under conjugation by `gamma = c^m` in `V_k` is infinite-dimensional.

For `k = 3` this applies to `w = [z, z^alpha]` with `z = [c^m, a^m]` and `alpha = a^m`, for every `m`.

**Consequences.**
- **The second-level eigen-shift program of Attempt 5 is dead one-sidedly.** A one-sided bound on the `gamma`-span in
  `A''/A''' ⊗ Q` would hold in `Q_3`. The candidate `[z, z^alpha]`, and any second-level element
  outside `P''`, has infinite span there. By `theta^2` the same holds for `alpha`-spans from the `d`
  side, for elements outside `P_d^(k-1)`, where `P_d = ncl_F(a)`.
- **`h(A'') = ∞` in `Q_k` for every `k >= 3`.** In `Q_3`, `A''` is abelian and `A'' ⊗ Q` is
  infinite-dimensional. `Q_k` maps onto `Q_3`, and Hirsch length does not increase under quotients. So
  the finite-Hirsch-length hypothesis of `solvable-by-metabelian-edge-images-collapse-higman-quotients`
  never follows from one side together with a derived-length bound.
- **Contrast with `k = 2`.** There `P/P^(k-2)` is trivial, so `gamma` acts trivially on `F'/P'`, and
  one-sided Step 2 succeeds. The obstruction starts exactly at derived length 3.

**What survives.** Collapse for derived length `k >= 3` needs a two-sided argument. Such an argument
bounds spans using both `b^a = b^2, c^b = c^2` and `d^c = d^2, a^d = a^2` before any layer is bounded.
One-sidedly, only elements of `P^(k-1)` (for the `gamma`-span) could still have finite span.
