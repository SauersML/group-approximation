---
rg: 2
id: kazhdan-linear-subspace-boundary-proof
kind: route
title: The projection onto W is a vector of the conjugation representation with no invariant vectors
target: kazhdan-reps-without-fd-subreps-have-linear-subspace-boundary
requires: []
---

Notation of the target. `HS(H)` is the Hilbert space of Hilbert--Schmidt operators on `H`, and
`sigma(g) X = pi(g) X pi(g)^*` is a unitary representation of `G` on it.

**Step 1: `sigma` has no nonzero invariant vector.** Suppose `X != 0` in `HS(H)` with
`pi(g) X pi(g)^* = X` for all `g`. Then `X` commutes with every `pi(g)`, and so does the compact
positive operator `T = X^* X != 0`. Take a nonzero eigenvalue `lambda` of `T`. Its eigenspace
`E_lambda` is finite-dimensional because `T` is compact, nonzero, and invariant under every
`pi(g)` because `T` commutes with `pi(g)`. So `pi` has a nonzero finite-dimensional
subrepresentation, against the hypothesis.

**Step 2: the Kazhdan inequality.** By Step 1 and the definition of a Kazhdan pair, every
`xi` in `HS(H)` satisfies `max_(q in Q) ||sigma(q) xi - xi||_HS >= kappa ||xi||_HS`. Apply it to
`xi = P_W`, the orthogonal projection onto `W`. Then `||P_W||_HS^2 = dim W` and
`sigma(q) P_W = P_(pi(q) W)`.

**Step 3: moving a projection costs at most twice the boundary.** Put `W' = pi(q) W` and
`V = W n W'`. Then

```text
||P_(W') - P_W||_HS^2 = tr P_(W') + tr P_W - 2 tr(P_(W') P_W) = 2 dim W - 2 tr(P_W P_(W') P_W).
```

The operator `Y = P_(W')` is positive and `P_V <= P_W`. Hence

```text
tr(P_W Y P_W) = tr(Y^(1/2) P_W Y^(1/2)) >= tr(Y^(1/2) P_V Y^(1/2)) = tr(P_V Y P_V) = tr P_V = dim V,
```

where `Y P_V = P_V` because `V <= W'`. So `||P_(W') - P_W||_HS^2 <= 2 (dim W - dim V) = 2 e_q(W)`.

**Step 4: conclusion.** Steps 2 and 3 give
`kappa^2 dim W <= max_q ||sigma(q) P_W - P_W||_HS^2 <= 2 max_q e_q(W)`. ∎

**The use remark.** If a map `rho(q)` on `W` agrees with `pi(q)` on `W_q <= W` with
`codim_W W_q <= B`, then `pi(q) W_q = rho(q) W_q <= W`, so `dim(W n pi(q) W) >= dim W_q >= dim W - B`
and `e_q(W) <= B`. So `dim W <= 2B / kappa^2`.
