---
rg: 2
id: fpbs-volume-uniform-activation-gate-log-law-proof
kind: route
title: Test the gate on two far-apart edges, where the activation increment is at least s^2 times the increment of a four-vertex spine event and X J X is at most 4 mu times its current value, then chain intervals on which the spine density grows by a fixed factor
target: fpbs-volume-uniform-activation-gate-log-law
requires:
  - fpbs-annealed-pivotal-factorization-off-spine-bridges
  - fpbs-spine-increment-activation-gate
  - fpbs-continuous-activation-collapse-family
---

Notation as in the target. For a frozen edge set `Z` and `r in [0,1]`, write
`Phi(r;Z)(x,y) = P(x <-> y in (xi_r ∪ Z) ∩ (Lambda ∪ Z))`, the probability over
`U` alone. Then `X^Lambda_t = E[Phi(t;Z_t)]` and
`D^A_{s,t} = E[Phi(s;Z_t) - Phi(s;Z_s)]`, as in
`fpbs-annealed-pivotal-factorization-off-spine-bridges`. `Phi(r;Z)` is
nondecreasing in `Z`, so `D^A >= 0`.

## 1. Theorem 1

Fix `Lambda = {e_1,e_2}` with `e_1 = {u,w}`, `e_2 = {v,w'}`, and
`d_G({u,w},{v,w'}) >= 2`. So `W = {u,w,v,w'}` has four distinct vertices,
and the only pairs in `W` joined by edges of `G` are `{u,w}` and `{v,w'}`.
For an edge set `Z` put

```text
A(Z) = { {u,w} ∩ V(Z) ≠ ∅ },    B(Z) = { {v,w'} ∩ V(Z) ≠ ∅ },
```

so `Psi(r) = P(A(Z_r) ∩ B(Z_r))`. Both events are increasing in `Z`.

**Step 1.1 (cross connections need both events).** Let `Z` be any edge set,
`r in [0,1]`, `x in {u,w}` and `y in {v,w'}`. If `x <-> y` in
`(xi_r ∪ Z) ∩ (Lambda ∪ Z)`, then `A(Z) ∩ B(Z)` holds. Hence
`Phi(r;Z)(x,y) <= 1_{A(Z) ∩ B(Z)}`.

*Proof.* Take a path from `x` to `y` in `Lambda ∪ Z`. The only edges of
`Lambda` are `e_1` and `e_2`, which are not joined to each other in
`Lambda`, so the path uses an edge of `Z`. Before its first `Z`-edge the path
uses only `e_1`, so the first endpoint of that edge is in `{u,w}` and in
`V(Z)`. Symmetrically, the last `Z`-edge has an endpoint in `{v,w'}`. ∎

**Step 1.2 (a lower bound when the spine is connected).** If `Z` is connected
(as a graph on `V(Z)`) and `s in [0,1]`, then
`Phi(s;Z)(u,v) >= s^2 1_{A(Z) ∩ B(Z)}`.

*Proof.* Suppose `A(Z) ∩ B(Z)` holds. If `u in V(Z)`, then `u` is joined to
`V(Z)` with probability `1`. Otherwise `w in V(Z)` and `e_1 ∉ Z`, since
`e_1 in Z` would put `u in V(Z)`. Then `u` is joined to `V(Z)` whenever
`U_{e_1} <= s`, which has probability `s`. The same holds for `v` with
`e_2`. The edges `e_1 ≠ e_2` carry independent labels. So with probability at
least `s^2`, both `u` and `v` are joined to `V(Z)` by open edges of the
volume. Since `Z ⊆ Lambda ∪ Z` is connected and open, `u <-> v`. ∎

**Step 1.3 (lower bound for `D^A`).** Condition on `M`. On the event
`E = (A(Z_t) ∩ B(Z_t)) \ (A(Z_s) ∩ B(Z_s))`, Step 1.1 gives
`Phi(s;Z_s)(u,v) = 0`. By (E2), `Z_t` is connected on `E`, since it is
nonempty there, so Step 1.2 gives `Phi(s;Z_t)(u,v) >= s^2`. Off `E`, the
difference `Phi(s;Z_t) - Phi(s;Z_s)` is nonnegative by monotonicity. Take
expectations. `A ∩ B` is increasing and `Z_s ⊆ Z_t`, so
`P(E) = Psi(t) - Psi(s)`, and

```text
D^A_{s,t}(u,v) >= s^2 (Psi(t) - Psi(s)).
```

**Step 1.4 (upper bound for `X J X`).** `J_W` is supported on the pairs
`(u,w)`, `(w,u)`, `(v,w')`, `(w',v)`, where `J_W <= mu`; the diagonal is zero,
because the identity is not a generator. So

```text
(X_t J_W X_t)(u,v) = J(u,w) [ X_t(u,u) X_t(w,v) + X_t(u,w) X_t(u,v) ]
                   + J(v,w') [ X_t(u,v) X_t(w',v) + X_t(u,w') X_t(v,v) ].
```

The entries `X_t(u,u)`, `X_t(v,v)`, `X_t(u,w)` and `X_t(w',v)` are at most
`1`. Each of `X_t(w,v)`, `X_t(u,v)` and `X_t(u,w')` is a cross connection,
which is at most `E[1_{A(Z_t) ∩ B(Z_t)}] = Psi(t)` by Step 1.1. Hence
`(X_t J_W X_t)(u,v) <= 4 mu Psi(t)`.

**Step 1.5.** If (AG_unif) holds on `{Lambda}` and `Psi(t) > 0`, then

```text
s^2 (Psi(t) - Psi(s)) <= D^A_{s,t}(u,v) <= kappa_A((s,t]) (X_t J_W X_t)(u,v) <= 4 mu Psi(t) kappa_A((s,t]),
```

which is the stated bound. ∎

## 2. Theorem 2

**Step 2.1 (a spine vertex at distance four).** Fix `r` with `m(r) > 0` and a
vertex `u`. On `{u in V(Z_r)}`, the graph `Z_r` is connected with infinitely
many vertices, by (E2). `G` is locally finite, so `V(Z_r)` contains vertices
at `G`-distance at least `4` from `u`. Walk along a path in `Z_r` from `u` to
such a vertex. The `G`-distance to `u` changes by at most `1` per step, so
the walk visits a vertex of the sphere `S_4(u)` that lies in `V(Z_r)`. Hence

```text
sum_{v in S_4(u)} P(u in V(Z_r), v in V(Z_r)) >= P(u in V(Z_r)) = m(r),
```

and since `|S_4(u)| <= d^4`, some `v_r in S_4(u)` has
`P(u, v_r in V(Z_r)) >= m(r)/d^4`.

**Step 2.2 (one interval).** Let `t_0 <= x < y <= t_1` with `m(x) > 0` and
`m(y) >= K m(x)`, where `K = 4 d^4`. Take `v = v_y` from Step 2.1, a
generator `g in S`, and `w = u g`, `w' = v g`. Then `d_G(u,v) = 4`, so
`d_G(w,v) >= 3`, `d_G(u,w') >= 3` and `d_G(w,w') >= 2`. Thus
`Lambda = {{u,w},{v,w'}} in 𝓛_2`. For the corresponding `Psi`:

* `Psi(y) >= P(u, v in V(Z_y)) >= m(y)/d^4`;
* `Psi(x) <= P({u,w} ∩ V(Z_x) ≠ ∅) <= 2 m(x)`, by invariance (E1).

So `1 - Psi(x)/Psi(y) >= 1 - 2 d^4 m(x)/m(y) >= 1 - 2 d^4 / K = 1/2`. By
Theorem 1, with `x >= t_0`,

```text
kappa_A((x,y]) >= (x^2/(4 mu)) · (1/2) >= t_0^2 / (8 mu).
```

**Step 2.3 (chaining).** Let `N = floor(log(m(t)/m(s)) / log K)`. Put
`x_0 = s`. For `i < N`, let `x_{i+1}` be the least `r in [x_i, t]` with
`m(r) = K m(x_i)`. It exists by continuity (E3) and the intermediate value
theorem, because `m` is nondecreasing and
`K^{i+1} m(s) <= K^N m(s) <= m(t)`. Then `x_{i+1} > x_i`, since
`m(x_i) > 0` and `K > 1`. The intervals `(x_i, x_{i+1}]` are disjoint and lie
in `(s,t]`, and Step 2.2 applies to each. Summing,

```text
kappa_A((s,t]) >= sum_{i<N} kappa_A((x_i,x_{i+1}]) >= N t_0^2 / (8 mu).
```

The second form follows from `N >= log(m(t)/m(s))/log K - 1`.

**Step 2.4 (the other gates).** By Theorem 2 (A) of
`fpbs-annealed-pivotal-factorization-off-spine-bridges`,
`D^A_{s,t} <= beta_s (S_t - S_s) beta_s`. So (AG*) with `kappa_A` on
`𝓛_2` implies (AG_unif) with the same `kappa_A`. The full gate with measure
`kappa` also implies it, since `D^A_{s,t} <= X_t - X_s`: indeed
`D^R_{s,t} = E[Phi(t;Z_t) - Phi(s;Z_t)] >= 0`, and
`X_t - X_s = D^R_{s,t} + D^A_{s,t}`. That identity is Theorem 2 there. It is
an exact telescoping identity and uses no connectivity. ∎

## 3. Corollary 3

`m(t_0) = 0` because `Z_{t_0} = ∅`. `m(t_1) > 0` because
`P(V(Z_{t_1}) ≠ ∅) > 0`, and by (E1) and countability of `V`. So
`s* = max{r in [t_0,t_1] : m(r) = 0}` exists by continuity and
monotonicity, and `s* < t_1`. For `s in (s*, t_1)` we have `m(s) > 0`, so
Theorem 2 gives `kappa_A((s*,t_1]) >= kappa_A((s,t_1]) >= c log(m(t_1)/m(s)) - t_0^2/(8 mu)`.
As `s ↓ s*`, continuity gives `m(s) -> 0`, so the right side tends to
infinity. ∎

## 4. Remarks

* **Why two edges.** A volume containing a single edge at each test vertex
  keeps `X J X` at the scale of the four-vertex spine event `Psi(t)`. The
  activation part, in turn, is at least `s^2` times the increment of that
  same event. The relative increment `(Psi(t)-Psi(s))/Psi(t)` is exactly the
  `dS/S` of the heuristic. In a large volume, `X J X` also contains
  `sum_{a~b} X(u,a) X(b,v)` over all spine-adjacent edges of the volume. That
  sum is unbounded in the volume, which is why the argument says nothing about
  a fixed exhaustion.
* **Sharper constant under decorrelation (not used).** Suppose the
  environment is mixing, for instance a factor of i.i.d. Then taking `v -> infinity`
  with the pattern `(u, ug, v, vg)` gives `Psi -> q^2`, with
  `q(r) = P({o,og} ∩ V(Z_r) ≠ ∅) in [m(r), 2m(r)]`. Then fine partitions give
  `kappa_A((s,t]) >= (t_0^2/(2 mu)) log(q(t)/q(s))`. The unconditional
  Theorem 2 does not need this.
