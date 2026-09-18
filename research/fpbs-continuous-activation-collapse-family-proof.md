---
rg: 2
id: fpbs-continuous-activation-collapse-family-proof
kind: route
title: Interpolate the nested spines through invariant geodesic forests with product-of-uniform levels, run the level threshold along a continuous strictly decreasing schedule, and anneal the single-edge jumps into integrable densities
target: fpbs-continuous-activation-collapse-family
requires:
  - fpbs-sharp-dominating-collapse-over-sparse-spines
  - fpbs-quenched-bk-russo-collapse-operator-gate
  - fpbs-soft-collapse-iff-invariant-sparse-spines
  - fpbs-hp-uniqueness-and-long-range-order
---

Notation as in the target. `(A_n)_{n >= 1}` and `n(t)` are the spines and the
schedule built in Steps 1-3 of `fpbs-sharp-dominating-collapse-over-sparse-spines-proof`
for the given `f`, `R`. We use only these facts about them:

* each `A_n` is an a.s. connected, infinite, invariant random subgraph, and
  `A_{n+1} ⊆ A_n`;
* `(A_n)` is independent of `U`;
* `P(o in V(A_n)) <= 3 · 2^-n`;
* for every fixed infinite connected vertex set `C`, `V(A_n) ∩ C ≠ ∅` a.s.,
  and this holds conditionally on `U` (Step 2 there);
* `n(t)` is deterministic, integer valued and nonincreasing on `(p_c,1]`,
  with `n(t) -> infinity` as `t ↓ p_c`, and it satisfies (3.1) there.

Since `P(o in V(A_n)) -> 0`, a.s. no vertex lies in every `V(A_n)`. On the
invariant null event where some vertex does, set all levels below to `0`.
Every statement below is almost sure.

## Step 1 (invariant geodesic forests between consecutive spines)

Take iid uniform labels `beta^n_x`, `V^n_x` (`n >= 1`, `x` a vertex) and
`gamma^n_e`, `W^n_e` (`n >= 1`, `e` an edge). They are independent of each
other, of the spine system and of `U`.

Fix `n`. For `x in V(A_n)` let `d_n(x)` be the graph distance in `A_n` from
`x` to `V(A_{n+1})`. It is finite because `A_n` is connected and
`V(A_{n+1}) ≠ ∅`.

For `x in V(A_n) \ V(A_{n+1})` (so `d_n(x) >= 1`):

* the **parent** `p_n(x)` is the `A_n`-neighbour `y` of `x` with
  `d_n(y) = d_n(x) - 1` that minimises `beta^n_y`;
* the **tree edge** `b_n(x)` is the edge of `A_n` between `x` and `p_n(x)`
  that minimises `gamma^n_e`, if there are parallel edges.

Ties have probability `0`. The construction is equivariant.

An edge `{x,y}` can be `b_n(x)` only if `d_n(y) = d_n(x) - 1`, and `b_n(y)`
only if `d_n(x) = d_n(y) - 1`. So **each edge is the tree edge of at most one
vertex**. Tree edges are not edges of `A_{n+1}`, because `x ∉ V(A_{n+1})`.

The **chain** of `x` is `x, p_n(x), p_n(p_n(x)), ...`, stopped before it
enters `V(A_{n+1})`. It has exactly `d_n(x)` vertices.

## Step 2 (levels)

For `x in V(A_n)` put

```text
lambda_n(x) = product of V^n_z over the chain of x     (x ∉ V(A_{n+1})),
lambda_n(x) = 1                                        (x in V(A_{n+1})).
```

So `lambda_n(x) = V^n_x lambda_n(p_n(x)) < lambda_n(p_n(x))` and
`lambda_n(x) in (0,1)` off `V(A_{n+1})`.

For `e in E(A_n) \ E(A_{n+1})` define its level:

```text
L_n(e) = lambda_n(x)                           if e = b_n(x) is a tree edge,
L_n(e) = W^n_e · min(lambda_n(a), lambda_n(b))  otherwise, where e = {a,b}.
```

In both cases `L_n(e) in (0,1)`. Every edge `e` of `A_1` lies in exactly one
difference `E(A_n) \ E(A_{n+1})`, because `∩ E(A_n) = ∅`. Put
`ell(e) = n + L_n(e) in (n, n+1)` there, and `ell(e) = 0` for `e ∉ E(A_1)`.

For real `sigma >= 1` let `𝒜_sigma` be the subgraph with edge set
`{e : ell(e) >= sigma}` and, as vertex set, the endpoints of those edges.

## Step 3 (properties of the interpolating spines)

Write `m = floor(sigma)` and `theta = sigma - m in [0,1)`.

**(i) Sandwich.** `A_{m+1} ⊆ 𝒜_sigma ⊆ A_m`, and `𝒜_m = A_m`.

Since `ell(e) in (k,k+1)` for `e in E(A_k) \ E(A_{k+1})`, we have
`ell(e) >= sigma` if and only if either `k >= m+1`, or `k = m` and
`L_m(e) >= theta`. With `theta = 0` this gives exactly `E(A_m)`.

**(ii) Monotone.** `𝒜_sigma` decreases in `sigma`. This is clear.

**(iii) Connected.** Take `theta > 0` (for `theta = 0` use (i)). Take an edge
`e in 𝒜_sigma` with `e in E(A_m) \ E(A_{m+1})`, so `L_m(e) >= theta`. It
suffices to join both endpoints of `e` to `V(A_{m+1})` inside `𝒜_sigma`,
since `A_{m+1}` is connected.

* If `e = b_m(x)`, then `p_m(x)` is an endpoint. Its level is
  `lambda_m(p_m(x)) > lambda_m(x) >= theta`. If `p_m(x) ∉ V(A_{m+1})`, then
  its tree edge `b_m(p_m(x))` has level `lambda_m(p_m(x)) >= theta`, so it is
  in `𝒜_sigma`. Iterating along the chain, which is finite, reaches
  `V(A_{m+1})` through edges of `𝒜_sigma`. The other endpoint is `x`, which
  is joined through `e` itself.
* Otherwise, let `e = {a,b}`. Then
  `min(lambda_m(a), lambda_m(b)) > W^m_e min(...) >= theta`. If
  `a ∉ V(A_{m+1})`, its tree edge `b_m(a)` has level `lambda_m(a) >= theta`,
  and we continue as in the first case. The same applies to `b`.

**(iv) Absolutely continuous levels.** Condition on the spines and on the
labels `beta`, `gamma`. This fixes all forests and chains. A tree level is
then a product of `k >= 1` independent uniforms, with density
`(-log y)^{k-1}/(k-1)!` on `(0,1)`. A non-tree level is `W` times an
independent positive variable. Both have absolutely continuous conditional
laws, so each `ell(e)` restricted to `(0,infinity)` has an absolutely
continuous law. Write `g_e` for its density on `[1,infinity)`.

**(v) Distinct levels.** For `e ≠ e'`, `P(ell(e) = ell(e')) = 0`.

* If they lie in different differences, their levels lie in disjoint
  intervals.
* If both are tree edges `b_n(x)`, `b_n(y)` with `x ≠ y`, their chains are
  different finite sets, which are fixed given `(A, beta, gamma)`. Take `z` in
  the symmetric difference, say in the chain of `x`. Conditioning on every
  `V` except `V^n_z` leaves an equation `V^n_z · c = c'`, where `c > 0` and
  `c'` are independent of `V^n_z`. This has probability `0`.
* If `e` is a non-tree edge, then `W^n_e` enters `ell(e)` and not `ell(e')`,
  and the same argument applies.

There are countably many pairs, so a.s. all positive levels are distinct.

## Step 4 (a continuous strictly decreasing schedule)

Put `u_k = p_c + 2^-k (1-p_c)` for `k >= 0`, and `b_k = n(u_{k+1}) + k + 1`.
Since `n` is nonincreasing and `u_k` is decreasing, `b_k` is strictly
increasing. Let `s : (p_c,1] -> [1,infinity)` be the function with
`s(u_k) = b_k` that is linear on each `[u_{k+1}, u_k]`. Then:

* `s` is continuous and strictly decreasing;
* `s(t) -> infinity` as `t ↓ p_c`;
* `s >= b_0 >= 1`;
* on `[u_{k+1}, u_k]`, `s(t) >= b_k >= n(u_{k+1}) >= n(t)`. So `s >= n` and
  `floor(s(t)) >= n(t)`, because `n` is an integer.

Define

```text
Z_t    = 𝒜_{s(t)}                                  (t in (p_c,1]),
tau_e  = inf{ t in (p_c,1] : ell(e) >= s(t) }       (inf ∅ = infinity).
```

Since `s` is a continuous decreasing bijection onto `[s(1), infinity)`, we get
`tau_e = s^{-1}(ell(e))` when `ell(e) >= s(1)`, and `tau_e = infinity`
otherwise. Also `Z_t = {e : tau_e <= t}`, and `tau_e > p_c`. The environment
is `M = (A_n, beta, gamma, V, W)`, which is independent of `U`, and every
`tau_e` is `M`-measurable. Put `omega_t = xi_t` for `t <= p_c`, and
`omega_t = xi_t ∪ Z_t` for `t > p_c`.

## Step 5 ((C0))

Steps 4-7 of `fpbs-sharp-dominating-collapse-over-sparse-spines-proof` use
`A_{n(t)}` only through the following properties. Each holds for `Z_t`.

1. **Connected and infinite.** This is Step 3(iii) and (i).
2. **Contains a spine.** `Z_t ⊇ A_{floor(s(t))+1}`, where the index is
   deterministic. So `V(Z_t)` meets every fixed infinite connected set a.s.,
   conditionally on `U`. This is used in the uniqueness step, applied to
   infinite `xi_t`-clusters.
3. **Sparse.** `V(Z_t) ⊆ V(A_{floor(s(t))}) ⊆ V(A_{n(t)})`. So
   `P(o in V(Z_t)) <= 3 · 2^-n(t)`. This is used in (H3) and (H4) through (3.1).
4. **Independent of `U`, with a deterministic schedule.** This is used in
   insertion tolerance (S3). Replacing `U_e` by `1` leaves `Z_t` unchanged.
5. **Monotone.** `Z_t` increases in `t` because `s` decreases. With
   `omega_t = xi_t` for `t <= p_c`, this gives (S1) and (S2).
6. **Ergodic.** The system is `Y' × Bern`, where `Bern` now also carries
   `beta`, `gamma`, `V`, `W`. This is a Bernoulli shift, and a product of an
   ergodic action with a mixing one is ergodic. This gives (S3).

Hence the structure lemma, uniqueness (S4), (H1)-(H5) and `theta_omega -> 0`
go through verbatim with `A_{n(t)}` replaced by `Z_t`. In particular
`T_t >= theta_xi(t)^2` entrywise for `t > p_c`, and
`P(e in Z_t) <= 3 · 2^-n(t) <= f(t)` on `(p_c, t_1]`.

## Step 6 ((C1), (C3))

**(C1).** Given `M`, `omega_t(e) = 1{U_e <= t} ∨ 1{tau_e <= t} = 1{U_e <= p_e(t)}`,
where `p_e(t) = 1` for `t >= tau_e` and `p_e(t) = t` otherwise. The `U_e` are
iid and independent of `M`, so the quenched law is a product measure with
densities `p_e(t) >= t`. Harris-FKG and BK-Reimer hold for product measures,
and the monotone coupling in `U` gives domination of `P_t`.

**Activation laws.** Let `F_e(t) = P(tau_e <= t) = P(ell(e) >= s(t))`. On
each linear piece of `s`, the change of variables `y = s(r)` gives
`F_e(t) - F_e(t') = ∫_{t'}^t g_e(s(r)) |s'(r)| dr`. Put
`rho_e(r) = g_e(s(r)) |s'(r)|`. As `t' ↓ p_c`,
`F_e(t') <= P(ell(e) >= s(t')) -> P(ell(e) = infinity) = 0`. Hence
`F_e(t) = ∫_{p_c}^t rho_e`, and `F_e` is absolutely continuous on `[p_c,1]`,
with `F_e = 0` on `[0,p_c]`. By Step 5(3), `∫_{p_c}^t rho_e = P(e in Z_t) <= 3 · 2^-n(t)`.

**Local events.** Let `E` be determined by a finite edge set `F_E`, and let
`s < t`. Then

```text
|P(omega_t in E) - P(omega_s in E)| <= P(omega_t ≠ omega_s on F_E)
                                   <= sum_{e in F_E} ( P(s < U_e <= t) + P(s < tau_e <= t) )
                                    = sum_{e in F_E} ∫_s^t (1 + rho_e).
```

So `t -> P(omega_t in E)` is absolutely continuous, and its a.e. derivative is
bounded by `sum_{e in F_E} (1 + rho_e)`. The laws of `U_e` and `tau_e` have no
atoms, so `P(omega_t ∩ Lambda ≠ omega_{t-} ∩ Lambda) = 0` for every `t`.
Taking `E = {u <-> v in omega ∩ Lambda}` shows that `T^Lambda` is entrywise
absolutely continuous on `[0,1]`.

## Step 7 ((C2), (C4), (C5))

**(C2).** By Step 3(v) and the injectivity of `s^{-1}`, the finite activation
times are distinct.

Fix `M` and finite `Lambda`. Between consecutive activation times in
`Lambda`, `tau^{M,Lambda}_t(u,v)` is a multilinear polynomial in the densities
`p_f(t)`, `f in Lambda`, each of which is `t` or `1`. By Russo's formula for
product measures, its derivative is the sum over the unactivated `f in Lambda`
of `P^M(f pivotal for u <-> v in omega_t ∩ Lambda)`.

For `f = {a,b}`, pivotality implies that `u <-> a` and `b <-> v` occur
disjointly in `(omega_t \ f) ∩ Lambda`, or the same with `a` and `b` swapped.
BK for the product measure gives the bound
`tau(u,a) tau(b,v) + tau(u,b) tau(a,v)`. Summing over `f` gives
`d/dt tau^{M,Lambda} <= tau^{M,Lambda} J tau^{M,Lambda}`.

At `r = tau_e` with `e in Lambda`, only `p_e` changes, from `r` to `1`. The
left limit `tau^{M,Lambda}_{r-}` is the value with `p_e = r`, because the
other densities are continuous at `r`. By linearity in `p_e`,

```text
tau_{r+}(u,v) - tau_{r-}(u,v) = (1-r) P^M_r(e pivotal for u <-> v in omega ∩ Lambda)
                             <= (1-r) ( tau_{r-}(u,a) tau_{r-}(b,v) + tau_{r-}(u,b) tau_{r-}(a,v) )
                              = (1-r) (tau_{r-} J_e tau_{r-})(u,v).
```

The inequality is the same BK bound in `omega \ e`, whose law is dominated by
the law at `r-`. The kernel `J_e` has operator norm `1`.

**(C4).** Take extra independent uniforms `U'_e`. For `0 <= t < t' <= 1`, put

```text
S_e = 1{t < U_e <= t'}                           if U_e > t,
S_e = 1{U'_e <= (t'-t)/(1-t)}                    if U_e <= t.
```

Given `M`, the values `1{U_e <= t}`, `(U_e ; U_e <= t)` and `U'`, each `S_e`
is Bernoulli`((t'-t)/(1-t))` independently. So `S` is independent of
`(M, (omega_s)_{s <= t})`. If `S_e = 1` then `e in xi_{t'}` or `e in xi_t`,
so `omega_t ∪ S ⊆ omega_{t'}`.

**(C5).** Local BK follows from (H4) exactly as (Q5) in
`fpbs-quenched-bk-russo-collapse-operator-gate`. On the event
`omega_t = xi_t` on `E(B_{R(t)})`, we have `{omega_t in E∘F} = {xi_t in E∘F}`.
BK holds for `xi_t`, and the ball laws differ by at most `f(t)` in total
variation.

## Proof of Theorem 2

**Item 2.** Fix `Lambda` and `u,v`.

* If `u = v`, or if `u` and `v` are not joined in the graph `Lambda`, the
  entry `T^Lambda(u,v)` is constant. Choose the version of its derivative to
  be `0` there.
* Otherwise let `a` be the neighbour of `u` on a path in `Lambda` from `u` to
  `v`. Then
  `(T^Lambda_r J T^Lambda_r)(u,v) >= T^Lambda_r(u,u) J(u,a) T^Lambda_r(a,v) >= r^{|Lambda|} >= p_c^{|Lambda|}`,
  since that path is open in `xi_r` with probability at least `r^{|Lambda|}`.
  By Step 6, `|dT^Lambda_r(u,v)/dr| <= sum_{e in Lambda} (1 + rho_e(r))`
  a.e.

Only finitely many entries are nonconstant. So
`C_Lambda <= p_c^{-|Lambda|} sum_{e in Lambda} (1 + rho_e)` a.e., which is
integrable because `∫ rho_e <= 1`.

**Item 1.** Use the conventions `0/0 = 0` and `x/0 = infinity` for `x > 0`.
`C*` is a countable supremum of Borel functions, so it is Borel.

Suppose `∫_{p_c}^{p_c+eps} C* < infinity`. Then `C* < infinity` a.e., and
`dT^Lambda_r/dr <= C*(r) T^Lambda_r J T^Lambda_r` entrywise a.e., for every
`Lambda`. Since each entry is absolutely continuous (Step 6),

```text
T^Lambda_t - T^Lambda_s = ∫_s^t dT^Lambda_r/dr dr <= ∫_s^t C*(r) T^Lambda_r J T^Lambda_r dr .
```

This is (G) on `[p_c, p_c+eps]` with `C = C*` and no atoms. At `t_0 = p_c`,
`omega_{p_c} = xi_{p_c}`, so `T_{t_0} = T_{p_c}` has finite norm. Theorem 2 of
`fpbs-quenched-bk-russo-collapse-operator-gate` then gives
`inf_{u,v} T_t(u,v) = 0` for all `t > p_c` close to `p_c`. This contradicts
`T_t >= theta_xi(t)^2 > 0` from (C0).

**Item 3.** Any integrable `C` and summable atoms satisfying (G) lead to the
same contradiction through the same Theorem 2. Here the true increments of
`T^Lambda` carry no atoms (Step 6). So atoms in (G) can only be slack, and
the jump estimate (b) of Corollary 3 there holds trivially with `m_k = 0`.

**Exact failing step.** Put `g_Lambda(t) = ||T^Lambda_t||`. `T^Lambda_t` is
the identity plus a finite matrix with continuous entries, so `g_Lambda` is
continuous. Also `g_Lambda(p_c) <= ||T_{p_c}||`, and `T^Lambda_t ↑ T_t` as
`Lambda ↑ E`, so `sup_Lambda g_Lambda(t) = ||T_t|| = infinity` for `t > p_c`
by (H5). Each `C_Lambda` is integrable, but by Item 1 `sup_Lambda C_Lambda`
is not.

## Proof of Proposition 3

Let `t > p_c` (the claim is meant for such `t`; the argument uses
`theta_xi(t) > 0`). Invariance is not needed. By Fubini, for a.e. `M` the
quenched product law `P^M` has a unique infinite cluster a.s. The event
`{u in an infinite cluster}` is increasing. So by Harris-FKG for `P^M`, and
domination by `P_t`,

```text
tau^M(u,v) >= P^M(u, v in the infinite cluster) >= P^M(u in inf. cl.) P^M(v in inf. cl.) >= theta_xi(t)^2 .
```

Suppose that with positive probability `sup_e p^M_e(t) < p_u`. Then for some
rational `q < p_u`, the event `B_q = {sup_e p^M_e(t) <= q}` has positive
probability. Pick `q' in (max(q,p_c), p_u)`, which exists because
`p_c < p_u`. On `B_q`, the `U`-coupling gives `omega_t ⊆ xi_{q'}`, so
`tau^M <= T_{q'}` entrywise. Bernoulli percolation at `q' in (p_c,p_u)` has
infinitely many infinite clusters. By `fpbs-hp-uniqueness-and-long-range-order`
(with `H = Gamma`), `inf_{u,v} T_{q'}(u,v) = 0`. This contradicts the display
for `M in B_q`.

So `sup_e p^M_e(t) >= p_u` a.s. for every `t > p_c` at which uniqueness holds.
For a collapse family this holds for all `t > p_c`, and the forced excess
`sup_e p^M_e(t) - t >= p_u - t` tends to `p_u - p_c`.

**Remark (why the smearing must be edge by edge).** A `Gamma`-invariant
random time that is measurable with respect to an ergodic system is a.s.
constant. So a construction that switches on an invariantly defined infinite
block at one common time switches it on at a deterministic time, which puts
an atom into the annealed kernels. That is the family of the operator gate.
The present family avoids this: its only simultaneous events are single
edges, and each edge has its own continuously distributed time.

**Remark (the split; not used above).** Formally,
`dT^Lambda/dr = R_r + A_r`. Here
`R_r(u,v) = E[ sum_{f in Lambda, tau_f > r} P^M_r(f pivotal) ]` is bounded by
`E[tau^M J tau^M]`, and
`A_r(u,v) = sum_{e in Lambda} rho_e(r) (1-r) E[ P^M_{r-}(e pivotal) | tau_e = r ]`.
Item 1 says `R + A` admits no integrable uniform ratio against `T J T`. Deciding
which of `R` and `A` carries this is the next step recorded in the target. ∎
