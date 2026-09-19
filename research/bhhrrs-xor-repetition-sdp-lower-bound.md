---
rg: 2
id: bhhrrs-xor-repetition-sdp-lower-bound
kind: claim
title: Every XOR game G with sdpval(G) > 1 - delta has l-fold parallel value val(G^l) > 1 - 4 sqrt(l delta) for every l (Barak--Hardt--Haviv--Rao--Regev--Steurer, FOCS 2008, Theorem 1.2)
distinct_from:
  raz-odd-cycle-repetition-lower-bound: that is the repeated-value lower bound for the single odd-cycle family; this is the general lower bound for every XOR game in terms of its SDP deficit, of which the odd cycle is the motivating case.
  akkstv-expansion-parallel-repetition-bound: that is an upper bound on repeated values via the Feige--Lovasz SDP; this is a lower bound on repeated values via rounding the basic SDP.
  black-box-repetition-needs-sqrt-scale-soundness-gap: that uses the odd cycle to kill universal repetition bounds; this supplies the SDP-deficit form of the same lower bound for every XOR game.
---

**ESTABLISHED, BY CITATION.** B. Barak, M. Hardt, I. Haviv, A. Rao, O. Regev
and D. Steurer, *Rounding Parallel Repetitions of Unique Games*, FOCS 2008,
Theorem 1.2 (proved as Theorem 4.10 with `s = 2`). Verbatim text is in
`bhhrrs-xor-repetition-sdp-lower-bound-citation`.

*Form used in this graph.* A unique game is a distribution over triples
`(u, v, π)`, and it is two-prover when the first and second supports are
disjoint. For such a game with alphabet `[2]`, `sdpval(G)` is the optimum of

```text
maximize  E_(u,v,π) Σ_(i in [2]) <u_i, v_π(i)>
s.t.      Σ_i ||u_i||^2 = 1,   <u_1, u_2> = 0     for every query u.
```

If `sdpval(G) > 1 − δ`, then `val(G^ℓ) > 1 − 4 sqrt(ℓ δ)` for every `ℓ in N`.

*Standard feasible point.* Fix a unit `e_0` and unit vectors `x_u ⊥ e_0`. Put
`u_1 = (e_0 + x_u)/2` and `u_2 = (e_0 − x_u)/2`. The constraints hold, and a
triple with sign `s = +1` (identity) or `s = −1` (swap) contributes
`(1 + s <x_u, x_v>)/2`. So the SDP deficit of this point is
`E_(u,v,s) (1 − s <x_u, x_v>)/2`.
