---
rg: 2
id: fpbs-sharp-dominating-collapse-over-sparse-spines-proof
kind: route
title: Take nested infinite clusters of an independent soft collapse family as spines, add harmonic-rate geodesic connectors from every vertex, and union with supercritical Bernoulli
target: fpbs-sharp-dominating-collapse-over-sparse-spines
requires:
  - fpbs-soft-collapse-iff-invariant-sparse-spines
  - fpbs-hermon-hutchcroft-supercritical-analyticity
  - fpbs-transitive-sharpness-linear-lower-bound
  - fpbs-critical-no-infinite-cluster
---

Notation as in the target. `G` is a Cayley graph, so the mass-transport
principle (MTP) holds for jointly invariant random functions. For a subgraph
`H`, `V(H)` is its vertex set. `B_R = B_R(o)`.

## Step 1 (nested independent spines)

By the hypothesis and Theorem A of `fpbs-soft-collapse-iff-invariant-sparse-spines`,
`G` carries a soft collapse family `(omega'_s)`, in an ergodic system `Y'`. Take
`Y'` independent of the labels `U`. For `s > p_c` let `I'_s` be the unique
infinite cluster of `omega'_s`, as a subgraph. Since `theta'(s) -> 0` as
`s ↓ p_c`, choose `s_1 > s_2 > ... ↓ p_c` with `theta'(s_n) <= 2^-n`, and put
`Omega_n = I'_{s_n}`.

* `Omega_n` is a.s. connected and infinite, its law is invariant, and
  `P(o in V(Omega_n)) <= 2^-n`.
* **Nested.** If `m >= n` then `s_m <= s_n`, so `omega'_{s_m} ⊆ omega'_{s_n}`.
  So `Omega_m` is an infinite connected subgraph of `omega'_{s_n}`, hence it
  lies in its unique infinite cluster: `Omega_m ⊆ Omega_n`.

## Step 2 (connectors from every vertex)

Take independent iid uniform labels `lambda^m_x` (`m >= 1`, `x in V(G)`) and
iid uniform tie-breaking labels `beta_x`, independent of `Y'` and `U`. For a
vertex `x` put `r_m(x) = d_G(x, V(Omega_m))`, which is finite a.s. Let
`gamma_m(x)` be the geodesic from `x` to a vertex of `V(Omega_m)` at distance
`r_m(x)` whose vertex label sequence `(beta)` is lexicographically minimal among
the finitely many candidates. It is a.s. well defined and equivariant. Put

```text
q_m(x) = 2^-m / (r_m(x)+1),
D_m    = ∪ { gamma_m(x) : lambda^m_x < q_m(x) },
A_n    = Omega_n ∪ ∪_{m >= n} D_m .
```

* **Connected, decreasing.** Each `gamma_m(x)` with `m >= n` ends in
  `V(Omega_m) ⊆ V(Omega_n)`, and `Omega_n` is connected, so `A_n` is connected
  and infinite. `A_{n+1} ⊆ A_n` because `Omega_{n+1} ⊆ Omega_n`.
* **Independent of `U`.** `A_n` is a function of `Y'`, `lambda` and `beta`.
* **Density.** From each `x` with `lambda^m_x < q_m(x)`, send mass `1` to each
  of the `r_m(x)+1` vertices of `gamma_m(x)`. Conditionally on `(Y',beta)` the
  expected mass sent from `o` is `q_m(o)(r_m(o)+1) = 2^-m`. The mass received
  at `o` is at least `1[o in V(D_m)]`. By the MTP, `P(o in V(D_m)) <= 2^-m`.
  Hence
  `P(o in V(A_n)) <= 2^-n + sum_{m>=n} 2^-m = 3 · 2^-n`.
* **`A_n` meets every infinite set that carries a path.** Let `C` be a fixed
  infinite connected set of vertices. By König's lemma `C` contains a simple
  infinite path `x_0, x_1, ...`, with `d_G(x_0,x_i) <= i`, so
  `r_n(x_i) <= r_n(x_0) + i` and
  `sum_i q_n(x_i) >= 2^-n sum_i 1/(r_n(x_0)+i+1) = infinity`. The labels
  `lambda^n_{x_i}` are independent of `(Y', beta, U)`, so by the second
  Borel--Cantelli lemma some `x_i` is selected a.s. Then
  `x_i in V(D_n) ⊆ V(A_n)`.

## Step 3 (the schedule `n(t)`)

Put `M(t) = sup_{s in [t,t_1]} chi^f_s` for `t in (p_c,t_1]`. It is finite by
`fpbs-hermon-hutchcroft-supercritical-analyticity` (continuity on the compact
interval `[t,t_1] ⊂ (p_c,1)`), and it is nonincreasing in `t`. Let
`g(t) = min(f(t), t-p_c)`, which is positive and nondecreasing. Define

```text
n(t) = max( ceil(1/(t-p_c)), ceil(log_2(3 max(M(t), |B_{R(t)}|) / g(t))) )   for t in (p_c,t_1],
n(t) = n(t_1)                                                                for t > t_1.
```

Each ingredient is monotone in the right direction, so `n` is nonincreasing.
Also `n(t) -> infinity` as `t ↓ p_c`, and for `t in (p_c,t_1]`

```text
3 · 2^-n(t) · chi^f_t <= g(t) <= f(t),     3 · 2^-n(t) · |B_{R(t)}| <= f(t).   (3.1)
```

## Step 4 (the family and (S1), (S2), (H1))

Put `omega_t = xi_t` for `t <= p_c` and `omega_t = xi_t ∪ A_{n(t)}` for
`t > p_c`. `xi_t` increases in `t`. `A_{n(t)}` increases in `t` because `n` is
nonincreasing and `A_n` decreases in `n`. So (S1) holds. (S2) and (H1) hold by
construction.

**Structure lemma.** Fix `t > p_c`, `n = n(t)`, and a cluster `K` of
`omega_t`. If `V(K) ∩ V(A_n) ≠ ∅` then `K ⊇ A_n`, so `K` is infinite.
Otherwise `K` contains no edge of `A_n`, since both endpoints of such an edge
lie in `V(A_n)`. So all its edges are `xi_t`-edges, and every `xi_t`-edge at a
vertex of `K` belongs to `K`. Hence `K` is a cluster of `xi_t` avoiding
`V(A_n)`.

## Step 5 (uniqueness, (H2))

**(S4), uniqueness.** `A_n` is infinite and connected, so it lies in one
infinite cluster. By the lemma, any other infinite cluster would be an
infinite `xi_t`-cluster `C` with `V(C) ∩ V(A_n) = ∅`. For each vertex `v`,
apply the last bullet of Step 2 conditionally on `(Y',beta,U)` to
`C = K^xi_t(v)` on `{|K^xi_t(v)| = infinity}`. It meets `V(A_n)` a.s. There
are countably many `v`, so a.s. there is exactly one infinite cluster.

**(H2).** By the lemma, for every finite `H` containing `o`,
`{K^omega_o = H} ⊆ {K^xi_o = H}`. So every bound
`E[F(K_o); |K_o| < infinity] <= B(t)` with `F >= 0` transfers from `xi_t` to
`omega_t`.

* With `F = 1[|H| >= n]` we get the exponential tail. Hermon--Hutchcroft,
  arXiv:1904.10448v3, abstract and Theorem 1.1: "if G is nonamenable and
  p>p_c(G) then there exists a positive constant c_p such that
  P_p(n≤|K|<∞)≤e^{−c_p n} for every n≥1".
* With `F(H) = |H|` we get `chi^f_omega(t) <= chi^f_t`.
* For the truncated two-point function, the event
  `{u <-> v in omega_t, |K^omega_u| < infinity}` is contained in
  `{u <-> v in xi_t, |K^xi_u| < infinity}`.

## Step 6 ((H3), (H4), (H5) and `theta_omega -> 0`)

**(H3).** If `K^xi_o` is finite and avoids `V(A_n)`, then by the lemma
`K^omega_o = K^xi_o` is finite. Therefore

```text
theta_omega(t) <= theta_xi(t) + P(|K^xi_o| < infinity, V(K^xi_o) ∩ V(A_n) ≠ ∅)
               <= theta_xi(t) + sum_x P_t(o <-> x, |K_o| < infinity) · P(x in V(A_n))
                = theta_xi(t) + chi^f_t · P(o in V(A_n))
               <= theta_xi(t) + 3 · 2^-n(t) chi^f_t  <=  theta_xi(t) + g(t).
```

The second line is a union bound and uses that `A_n` is independent of `U`.
The third uses invariance, and the last uses Step 2 and (3.1). The lower bound
is (H1). The consequence `theta_omega/theta_xi -> 1` for `f(t) = (t-p_c)^2`
follows from `theta_xi(t) >= K(t-p_c)` (`fpbs-transitive-sharpness-linear-lower-bound`).

**`theta_omega -> 0`.** `theta_xi(t) = inf_R P_t(o <-> ∂B_R)` is an infimum of
polynomials in `t`, so it is upper semicontinuous. Hence
`limsup_{t ↓ p_c} theta_xi(t) <= theta_xi(p_c) = 0` by
`fpbs-critical-no-infinite-cluster`, and `g(t) <= t - p_c -> 0`.

**(H4).** If `omega_t` and `xi_t` differ on `E(B_R)`, some edge of `A_n` lies in
`E(B_R)`, so some vertex of `B_R` lies in `V(A_n)`. The union bound gives
probability at most `|B_R| · 3 · 2^-n(t) <= f(t)` at `R = R(t)`, by (3.1).

**(H5).** The unique infinite cluster of `omega_t` contains every infinite
`xi_t`-cluster. So
`P(u <-> v in omega_t) >= P_t(u in I(xi_t), v in I(xi_t)) >= theta_xi(t)^2`,
by Harris--FKG for the product measure. Summing over `u,v in B_R` gives
`<1_{B_R}, T^omega_t 1_{B_R}> >= theta_xi(t)^2 |B_R|^2`, so
`||T^omega_t||_{2->2} >= theta_xi(t)^2 |B_R| -> infinity`.

## Step 7 ((S3))

**Insertion tolerance.** Fix `t > 0`, an edge `e` and an event `B`, and write
`Pi_e B = {w ∪ {e} : w in B}`. If `t <= p_c`, `omega_t` is Bernoulli and the
claim is standard. If `t > p_c`, let `omega'` be `omega_t` computed with `U_e`
replaced by `1`. The deterministic `n(t)` and the `U`-independent `A_{n(t)}`
are unchanged, so `omega'` is independent of `U_e`, `omega_t ∪ {e} = omega' ∪ {e}`,
and `omega_t = omega' ∪ {e}` on `{U_e <= t}`. Hence

```text
P(omega_t in Pi_e B) >= P(U_e <= t, omega' ∪ {e} in Pi_e B) = t · P(omega' ∪ {e} in Pi_e B) >= t · P(omega_t in B).
```

The last inequality holds because `omega_t in B` implies
`omega' ∪ {e} = omega_t ∪ {e} in Pi_e B`.

**Ergodicity.** The system is `Y' x Bern`, where `Bern` is the Bernoulli shift
carrying `U`, `lambda` and `beta` (a countable family of iid labels permuted by
`Gamma`). `Y'` is ergodic by (S3) of the imported family. A Bernoulli shift of
an infinite countable group is mixing, hence weakly mixing, and the product of
an ergodic action with a weakly mixing action is ergodic.

## Corollary

`T_3 x Z`, closed hyperbolic mapping tori and `F_2 x Z` satisfy the spine
hypothesis by Theorem B of `fpbs-soft-collapse-iff-invariant-sparse-spines`.
They have `p_c < p_u` for the (respectively all, all, some) generating sets
recorded in its Corollary C. Suppose an argument used only the inputs 1--5 of
the target. It would apply verbatim to `omega` with any `f`, `R` that the
argument fixes in advance, and would give `p_u(omega) > p_c`. But (S4) gives
uniqueness for every `t > p_c`. The failing step is therefore the passage from
these inputs to a nontrivial **upper** bound on some increasing connection
event at unbounded range for `t > p_c`, or to mixing or deletion tolerance.
None of these holds for `omega`: `P(u <-> v in omega_t) >= theta_xi(t)^2`
for all `u, v`, and the spine `A_n` cannot be closed edge by edge. ∎
