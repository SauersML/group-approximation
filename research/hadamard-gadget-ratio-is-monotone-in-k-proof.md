---
rg: 2
id: hadamard-gadget-ratio-is-monotone-in-k-proof
kind: route
title: Diagonal restriction f(y, y) turns a level-(k+1) adversary into a level-k adversary at twice the per-edge cost
target: hadamard-gadget-ratio-is-monotone-in-k
requires: [hadamard-gadget-deletion-ratio-window]
artifacts:
  - experiments/ugc-hadamard-limit-2026-09-17/check_monotone_lift.py
---

**The map.** Write `F_2^(k+1) = F_2^k x F_2`, with coordinates `(i, u)`.
Define `iota : Q_k -> Q_(k+1)` by `iota(y)_(i,u) = y_i`.

**Four facts.** `check_monotone_lift.py` verifies all four exhaustively for
`k <= 3`. Each one is also immediate.

* (F1) `iota(-y) = -iota(y)`.
* (F2) `iota(chi_a) = chi_(a,0)`, because `(a,0).(i,u) = a.i`. The map
  `a -> (a,0)` is injective and sends `a != 0` to a nonzero vector.
* (F3) For each `y` and coordinate `j`, the images `iota(y)` and `iota(y^j)`
  differ exactly in the coordinates `(j,0)` and `(j,1)`. Let `m` be `iota(y)`
  with `(j,0)` flipped. Then `iota(y) - m - iota(y^j)` is a path of two
  length-one edges in `Q_(k+1)`.
* (F4) `iota` is injective.

**The lift.** The minimum defining `z*(P_(k+1))` is over a compact convex set
of distributions and is attained. Let `nu` be an optimal adversary, so every
length-one edge of `Q_(k+1)` is cut with probability at most
`z = z*(P_(k+1))`. Draw `f ~ nu` and set `g = f o iota`.

* **Folded.** `g(-y) = f(-iota y) = -f(iota y) = -g(y)`, by (F1).
* **Random on `P_k`.** `(g(chi_a))_a = (f(chi_(a,0)))_a` by (F2). This is a
  sub-vector of the uniformly random vector `(f(chi_b))_b`, so it is uniform.
  The sign of each pin is then fixed by folding. For `P'_k` use only
  `a != 0`, which (F2) sends inside `P'_(k+1)`.
* **Edge cost.** For an edge `(y, y^j)`, (F3) and a union bound give
  `Pr[g(y) != g(y^j)] <= Pr[f(iota y) != f(m)] + Pr[f(m) != f(iota y^j)] <= 2z`.

**Conclusion.** `g`'s law is feasible at level `k` with maximum edge cost at
most `2z`, so `z*(P_k) <= 2 z*(P_(k+1))`. Multiplying by `K = 2^k` gives
`R*(k) = K z*(P_k) <= 2K z*(P_(k+1)) = R*(k+1)`.

**The consequences.** Items 1 to 5 of the claim follow from monotonicity
together with the bounds cited there. A bounded monotone sequence converges to
its supremum. `R*(k) <= 5/2 - 2^(1-k) < 5/2`, and
`R*(4) >= 331440289/227504128`.
