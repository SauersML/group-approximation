---
rg: 2
id: rotated-frame-universe-discretisation-proof
kind: route
title: Push U_n forward along a fine finite Borel partition and use cell representatives as SDP vectors
target: rotated-frame-universe-discretises-to-robust-rich-2to1-sdp-gaps
requires: []
artifacts:
  - experiments/rich-2to1-rotated-frame-universe-2026-09-17/check_universe_identities.py
---

Fix `n` and `eta > 0`. Put `eps = eta / 8`.

**Step 1 (cells).** `O(2n)` and the Stiefel manifold `V_n(R^(2n))` are compact.
Metrize both by the maximum row distance. Choose finite Borel partitions
`{C_c}` of `O(2n)` and `{D_d}` of `V_n(R^(2n))` with every cell of diameter at
most `eps`. Pick a representative `X_c in C_c` and `Y_d in D_d` in each cell.

**Step 2 (instance).** Left vertices are the cells `c` and right vertices are
the cells `d`. For each ordered pairing `P` there is an edge `(c, d, P)` with
constraint `pi_P` and weight `W(c,d,P) = Pr[X in C_c, Y in D_d, P]` under the
edge law of `U_n`. Parallel edges with different `P` are allowed, as in any
weighted Label Cover instance. The instance is rich because
`Pr[P | X in C_c] = 1/(number of ordered pairings)`, by independence of `P`
and `X`.

**Step 3 (value).** Take a labelling `f : cells -> [2n]`, `g : cells -> [n]`.
It lifts to the Borel strategy `f o cell`, `g o cell` on `U_n`. The lift
satisfies exactly the same mass, since `W` is the pushforward of the edge law.
Hence `val(G) <= val(U_n)`.

**Step 4 (SDP).** Put `z(c,a) = x_(c,a)/sqrt(2n)` and `z(d,b) = y_(d,b)/sqrt(n)`.
Norms sum to 1 and within-vertex vectors are orthogonal, because
representatives are frames. Take any point `(X, Y, P)` counted in `W(c,d,P)`.
Its exact objective is `sum_a <x_a, y_(pi(a))>/(sqrt2 n) = 1`. Replacing
`x_a, y_b` by the representatives changes each inner product by at most `2 eps`,
since all vectors are unit and the cells have diameter at most `eps`. Summed
over the `2n` labels, the loss is at most `2n * 2 eps/(sqrt2 n) = 2 sqrt2 eps`.
Averaging over `W`, the basic SDP value is at least `1 - 2 sqrt2 eps`.

**Step 5 (rational weights, if an unweighted instance is wanted).** Round
`Pr[X in C_c]` and each conditional law of `d` given `(c, P)` to rationals
with a common denominator, keeping `Pr[P | c]` exactly uniform. This moves at
most `eps` of total weight, so value and SDP value each move by at most `eps`.
Duplicating edges by multiplicity gives an unweighted rich multigraph instance.

In total, the basic SDP value is at least `1 - 2 sqrt2 eps - eps >= 1 - eta`
and `val <= val(U_n) + eps <= val(U_n) + eta`.

The corollary is immediate. The instance has basic SDP `>= 1 - eta_0` whenever
`eta <= eta_0`, and value at most `delta + eta`.
