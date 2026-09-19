---
rg: 2
id: fpbs-spread-out-uniqueness-gives-sparse-spines-proof
kind: route
title: Realise every open edge of the unique spread-out cluster by a fixed S-geodesic, pay p squared b per interior vertex, then feed the spine to the cost bound
target: fpbs-spread-out-uniqueness-gives-sparse-spines
requires:
  - fpbs-sparse-spine-cost-bound
  - fpbs-fiid-soft-collapse-iff-fiid-sparse-spines
  - fpbs-bernoulli-cayley-cost-above-one-forces-nonuniqueness
---

Written derivation. Cayley graphs have edges `{g, gs}`, `Gamma` acts on the left, `d = |S|`, `D = |T|`.

**Step 0 (labels).**
- Let `x = (x(h))_(h in Gamma)` be iid uniform on `[0,1]`. Split each `x(h)` by binary digits into independent
  uniforms `x(h)_0, x(h)_1, ...`, as in Step 0 of
  `fpbs-bernoulli-cayley-cost-above-one-forces-nonuniqueness-proof`.
- Write `T = T^+ ⊔ T^- ⊔ T^2`, where `T^- = (T^+)^-1` and `T^2` consists of the involutions of `T`. Fix an
  injection `i : T^+ ⊔ T^2 -> {1,2,...}`.
- Vertex `h` is open iff `x(h)_0 < p`.
- The `T`-edge `{h, ht}` is open iff its label is `< b`. Its label is:
  - `x(h)_(i(t))` for `t in T^+`;
  - the fractional part of `x(h)_(i(t)) + x(ht)_(i(t))` for `t in T^2`.
- For each `t in T^2` the `t`-edges form a perfect matching, so every uniform is used by exactly one edge. All vertex
  and edge labels are therefore iid uniform, and `omega_(p,b)` is a `Gamma`-equivariant measurable function of `x`.
  Left multiplication by `g` maps the edge `{h,ht}` to `{gh,ght}` and carries labels along.

**Step 1 (the cluster is a factor).**
- `{h is in an infinite open cluster}` is a countable intersection over `R` of the events "there is an open path
  from `h` to the complement of `B_T(h,R)`". Each of these is measurable.
- So the set `C` of vertices in infinite clusters is an equivariant measurable function of `x`.
- In the uniqueness phase `C` is a.s. one infinite cluster, connected through open `T`-edges between open vertices.
- `P(o in C) = theta_T(p,b) <= P(o open) = p`.

**Step 2 (fixed geodesic words).**
- For each `t in T^+ ⊔ T^2`, fix an `S`-geodesic word `w_t = s_1 ... s_(l_t)`, with `l_t = |t|_S <= L`. For
  `t in T^-`, let `w_t` be the inverted reversal of `w_(t^-1)`.
- For `x in Gamma` and `t in T`, let `P(x,t)` be the `S`-path
  `x, x s_1, x s_1 s_2, ..., x t`. Its interior is the set of vertices at positions `j = 1, ..., l_t - 1`.
- Left equivariance: `g P(x,t) = P(gx,t)`.
- For `t in T^+ ⊔ T^-`, `P(x,t)` and `P(xt,t^-1)` have the same vertex set. For `t in T^2`, both paths `P(x,t)`
  and `P(xt,t)` are used below.

**Step 3 (the spine).** Put

```text
V' = C ∪ ⋃ { interior of P(x,t) : x in Gamma, t in T, x in C, xt in C, the edge {x,xt} is open }.
```

- `V'` is an equivariant measurable function of `x`, so it is FIID.
- *Connected.* Any two vertices of `C` are joined by an open `T`-path inside `C`. Replacing each `T`-edge
  `{x,xt}` of that path by `P(x,t)` gives an `S`-path inside `V'`. Every vertex of `V' \ C` lies on such a path
  whose ends are in `C`. So the subgraph of `Cay(Gamma,S)` induced on `V'` is connected.
- *Infinite.* It contains `C`.

**Step 4 (density; Theorem A).**
- Suppose `o` is interior to `P(x,t)` at position `j`. Then `x = (s_1 ... s_j)^-1`, so `x` is determined by
  `(t,j)`.
- The number of pairs `(t,j)` is `sum_(t in T) (l_t - 1) <= |T| (L-1)`.
- For each pair, `o in V'` through that path requires `x` open, `xt` open (distinct from `x`, since `e ∉ T`) and
  the edge `{x,xt}` open. By independence this has probability `p^2 b`.
- By the union bound,

  ```text
  P(o in V') <= P(o in C) + p^2 b |T| (L-1) <= theta_T(p,b) + p^2 b |T| (L-1) <= p + p^2 b |T| (L-1).
  ```

**Step 5 (Corollary B).**
- Let `S'` be any finite symmetric generating set, and let `c = max_(s in S) |s|_(S')`. Then `T_k ⊂ B_(S')(c L_k)`.
- Steps 3 and 4 applied with `S'` give FIID a.s. connected infinite subgraphs of `Cay(Gamma,S')` with density at most
  `p_k + c p_k^2 b_k |T_k| L_k -> 0`. So `Gamma` has FIID sparse spines on every Cayley graph.
- The three consequences are the cited theorems:
  - `fpbs-sparse-spine-cost-bound` gives `C* <= 1 + (d/2-1) eps` for every `eps`, so `C* = 1`;
  - Theorem 1 of `fpbs-bernoulli-cayley-cost-above-one-forces-nonuniqueness` gives `C_sub^b(S') = 1` and
    `beta_1 = 0`;
  - Corollary E of `fpbs-fiid-soft-collapse-iff-fiid-sparse-spines` gives the obstruction to soft proofs.

**Step 6 (Corollary C).**
- *The value of `eps_0` when `C* > 1`.* By `fpbs-sparse-spine-cost-bound`, an FIID connected infinite vertex set of
  density `theta` gives `C* <= 1 + (d/2 - 1) theta`. So, for `d >= 3`, `theta >= (C* - 1)/(d/2 - 1)`. A group with
  `d <= 2` is virtually cyclic, has `C* = 1`, and the hypothesis is vacuous.
- *The inequality on the uniqueness phase.* At every `(p,b)` in the mixed uniqueness phase, Theorem A gives a spine
  of density at most `p + p^2 b |T| (L-1)`, so this quantity is `>= eps_0`.
- *The bound on `p_u^site`.* Put `b = 1` and `f(p) = p + p^2 |T| (L-1)`. This `f` is continuous and increasing on
  `[0,1]`.
  - Let `U` be the set of site-uniqueness parameters. If `U` is empty, then `p_u^site = 1` and the bound holds
    trivially.
  - Otherwise `eps_0 <= inf_U f = f(inf U) = f(q)`, where `q = p_u^site(T)`. No monotonicity of uniqueness is used.
  - If `L = 1`, then `q >= eps_0`.
  - If `L >= 2` and `q < eps_0/2`, then `q^2 |T| (L-1) >= eps_0/2`, so `q >= (eps_0/(2|T|(L-1)))^(1/2)`.

**Step 7 (Calibration D).**
- *Path-counting bound.* On the `D`-regular graph `Cay(Gamma,T)`, with `P` the simple random walk operator and
  `rho_T = ||P||`, the event `o <-> x` needs an open self-avoiding path. So

  ```text
  tau_p(o,x) <= sum_(n >= |x|_T) p^(n+1) D^n P^n(o,x) <= p sum_(n >= |x|_T) (p D rho_T)^n .
  ```

  This uses `P^n(o,x) <= ||P||^n`, since `P` is self-adjoint.
  - If `p D rho_T < 1`, then `tau_p(o,x) -> 0` as `|x| -> infinity`.
  - Uniqueness with `theta > 0` gives `tau_p(o,x) >= theta^2` by Harris–FKG.
  - Hence `p_u^site(T) >= 1/(|T| rho_T)`.
- *The free group.* On `F_2` with a free basis, the Cayley graph is the 4-regular tree, `q = 3`. The operator
  `lambda(chi_(T_L))` is a polynomial in `A = lambda(chi_(S_1))`, namely `sum_(m=1)^L chi_m(A)`, where the `chi_m`
  are the sphere polynomials: `chi_2 = A^2 - (q+1)` and `chi_(m+1) = A chi_m - q chi_(m-1)`.
  - Kesten: `spec(A) = [-2 sqrt q, 2 sqrt q]`.
  - So `|T| rho_T = max_(z in spec A) |sum_m chi_m(z)|`.
  - The maximum is attained at `z = 2 sqrt q`, where `chi_m(2 sqrt q) = |S_m| (1 + m (q-1)/(q+1)) q^(-m/2)`
    (Haagerup's ground spherical function).
  - The script checks the grid maximum against this closed form for `L <= 14`; they agree to printed precision.
- *The comparison.* The script prints both lower bounds for `L = 2, ..., 20`. The cost bound is larger at every `L`.
  Their ratio is `2.03` at `L = 2` and `3.73` at `L = 20`.
  - Asymptotics: `|T| rho_T ~ (4/3)(1 + L/2) 3^(L/2)/(1 - 3^(-1/2))` and `|T| ~ 2·3^L`.
  - So the ratio is `~ sqrt(L)/(3(1 - 3^(-1/2))) ≈ 0.79 sqrt(L)`.
