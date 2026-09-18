---
rg: 2
id: gaussian-universe-polar-frame-discretisation-proof
kind: route
title: Send the polar-frame objective to 1 by the law of large numbers and bounded convergence, then push the Gaussian universe forward along fine cells of the two polar frames and use cell representatives as SDP vectors
target: gaussian-universe-discretises-to-robust-rich-2to1-sdp-gaps
requires: []
artifacts:
  - experiments/gaussian-rich-2to1-universe-2026-09-17/check_gaussian_universe.py
---

Notation is as in the target.

**Step 0 (the vectors are feasible and the formula holds).** The columns of
`polar(G)` are orthonormal, so the left vectors are pairwise orthogonal, with
squared norms summing to `2n/(2n) = 1`. The right vectors behave the same way,
with sum `n/n = 1`. Also

`polar(G)^T polar(H) = (G^T G)^(-1/2) G^T G M_P (M_P^T G^T G M_P)^(-1/2)`,

and the factors of `d` cancel. Dividing by `sqrt(2n) sqrt(n) = sqrt2 n` gives
the formula for `o`. Every entry of a product of two matrices with orthonormal
columns has absolute value at most 1, so `|o| <= 2n/(sqrt2 n) = sqrt2`.

**Step 1 (item 1).** Realise `G` for all `d` as the top `d` rows of one
infinite iid `N(0,1)` array with `2n` columns. The law of `o` depends only on
`d` and on the law of `Sigma`, so this coupling is allowed. By the strong law
of large numbers, `Sigma -> I` almost surely. The map
`Sigma -> Sigma^(1/2) M_P (M_P^T Sigma M_P)^(-1/2)` is continuous on positive
definite matrices. At `Sigma = I` it equals `M_P (2 I_n)^(-1/2) = M_P/sqrt2`,
whose `(a, P(a))` entries are `1/sqrt2`. So `o -> 2n/(sqrt2 sqrt2 n) = 1`
almost surely, for each of the finitely many `P`. Since `|o| <= sqrt2`,
bounded convergence gives `E o -> 1`.

**Step 2 (item 2: cells).** The Stiefel manifolds `V_(2n)(R^d)` and
`V_n(R^d)` of orthonormal column tuples are compact. Metrise each by the
maximum column distance. Choose finite Borel partitions `{C_c}` and `{D_e}`
with every cell of diameter at most `eps`, and a representative in each cell.

**Step 3 (instance).** Left vertices are the cells `c`, and right vertices are
the cells `e`. For each labelled 2-to-1 map `P` there is an edge `(c, e, P)`
with constraint `P` and weight

`W(c, e, P) = Pr[polar(G) in C_c, polar(G M_P) in D_e, P]`.

It is rich: `P` is independent of `G`, so `Pr[P | polar(G) in C_c]` is uniform.

**Step 4 (value).** A labelling `f` of left cells and `g` of right cells lifts
to the Borel strategy `A = f o cell o polar`, `B = g o cell o polar` of
`Gamma_(n,d)`. Acceptance depends only on `(cell(polar G), cell(polar H), P)`,
and `W` is the pushforward of the edge law. So the lift wins with exactly the
instance's success probability, and `val <= val(Gamma_(n,d))`.

**Step 5 (SDP).** Use the representatives, scaled as in the target, as the
SDP vectors. Feasibility is Step 0 applied to the representatives. At any
point `(G, P)` counted in `W(c, e, P)`, swapping the exact polar columns for
the representatives changes each unit inner product by at most `2 eps`. Over
the `2n` labels the objective changes by at most `2n * 2 eps/(sqrt2 n) = 2 sqrt2 eps`.
Averaging over `W`, the SDP value is at least `E o - 2 sqrt2 eps`.

**Step 6 (rational weights, optional).** This is Step 5 of
`rotated-frame-universe-discretisation-proof`, verbatim. Round `Pr[cell c]`
and the conditional laws of `e` given `(c, P)` to a common denominator, keeping
`Pr[P | c]` exactly uniform. Value and SDP each move by at most `eps`.
Duplicating edges then gives an unweighted rich multigraph.

**Use.** Given `eta`, pick `d` with `E o >= 1 - eta/2` (Step 1) and take
`eps = eta/8`. The SDP value is then at least
`1 - eta/2 - (2 sqrt2 + 1) eta/8 >= 1 - eta`, and the value is at most
`val(Gamma_(n,d)) + eta`.
