---
rg: 2
id: fpbs-nonunimodular-level-sets-break-identity-e-proof
kind: route
title: The modular homomorphism, the tilted mass-transport principle and a Schur-Folner norm computation put the quotient l2 threshold at p_T and the level-set relative threshold above p_t
target: fpbs-nonunimodular-level-sets-break-identity-e
requires:
  - fpbs-hutchcroft-nonunimodular-pc-below-pt
  - fpbs-hyperbolic-and-nonunimodular-nonuniqueness
---

Complete written proof. Notation is as in the target. All sums are of
nonnegative terms and take values in `[0,infinity]`, so Tonelli applies
throughout.

**Imports.**

- `fpbs-hutchcroft-nonunimodular-pc-below-pt` (ESTABLISHED, imported): the
  definitions of `Delta`, `chi_(p,lambda)`, `p_c(G,Gamma,lambda)` and
  `p_t = p_c(G,Gamma,1/2)`, base-point independence of `chi_(p,lambda)(v)`,
  and `thm:pcpt`.
- Two more verbatim statements from the same TeX source
  (arXiv:1711.02590v3, `NonunimodularPercolation_Revised5.tex`, read
  2026-09-19), used only for the general parts 1-4:
  - lines 277-279: "The \textbf{tilted mass-transport principle} states that
    if $F:V^2\to[0,\infty]$ is invariant under the diagonal action of
    $\Gamma$, meaning that that $F(x,y)=F(\gamma x, \gamma y)$ for every
    $\gamma \in \Gamma$, then \[\sum_{v\in V} F(x,v) = \sum_{v\in V} F(v,x)
    \Delta(x,v)\] for every $x\in V$."
  - `lem:modularsymmetries`, lines 784-792: "Let $G$ be a connected, locally
    finite graph, and let $\Gamma \subseteq \Aut(G)$ be quasi-transitive.
    Then the modular function ... has the following properties. ... $\Delta$
    is $\Gamma$-diagonally invariant. ... $\Delta$ satisfies the
    \textbf{cocycle identity} \[\Delta(u,v)\Delta(v,w) = \Delta(u,w)\] ... In
    particular, $\Delta(u,u)=1$ and $\Delta(u,v)=\Delta(v,u)^{-1}$". The source
    proves the cocycle identity from Lyons--Peres, Theorem 8.10.
  - line 277 also records "$\Gamma$ is unimodular if and only if
    $\Delta(x,y) \equiv 1$".
- `fpbs-hyperbolic-and-nonunimodular-nonuniqueness` (ESTABLISHED, imported):
  `p_c < p_h <= p_u` for transitive nonunimodular `Gamma`. It is used only to
  see that the interval `(p_c, min{p_t,p_u})` in the C3 bullet of the target
  is nonempty.
- Classical tree facts, used only in part 5: `p_c(T_k) = 1/(k-1)` and
  `p_u(T_k) = 1` (Lyons--Peres, *Probability on Trees and Networks*, Ch. 5
  and Ch. 7).

## Part 1. Structure

**(1a) Homomorphism.** For `gamma, eta in Gamma`, the cocycle identity and
diagonal invariance give
`delta(gamma eta) = Delta(o,gamma o) Delta(gamma o, gamma eta o) = delta(gamma) delta(eta)`.
For any `x`,
`Delta(x, gamma x) = Delta(x,o) Delta(o,gamma o) Delta(gamma o, gamma x) = Delta(x,o) delta(gamma) Delta(o,x) = delta(gamma)`.
So `N_Delta = ker delta` is normal, and `Gamma/N_Delta ≅ D`. `D` is a subgroup
of the multiplicative group `(0,infinity)`, so it is abelian, and it is
countable because its values are ratios of orbit sizes. A countable abelian
group is amenable.

**(1b) Stabilizers.** If `gamma y = y`, then
`delta(gamma) = Delta(y, gamma y) = Delta(y,y) = 1`. So every stabilizer
`Gamma_y` lies in `N_Delta`.

**(1c) Orbits are level sets.** Write `y = gamma o` and `z = eta o`. Then
`Delta(o,y) = delta(gamma)`, so `z` and `y` lie in the same level set iff
`gamma^(-1) eta in N_Delta`, iff `z in gamma N_Delta o = N_Delta gamma o`.
So `L_c = N_Delta y` for any `y` with `Delta(o,y) = c`, and
`L_c = gamma L_1` for any `gamma` with `delta(gamma) = c`. In particular all
level sets have the cardinality of `L = L_1`, and they are indexed by `D`.

**(1d) Nontrivial.** `Gamma` is nonunimodular, so `Delta(x,y) != 1` for some
`x,y`. Choose `eta` with `eta o = x`. By invariance
`Delta(o, eta^(-1) y) = Delta(x,y) != 1`, and `eta^(-1) y = gamma o` for some
`gamma`, so `delta(gamma) != 1`.

**(1e) `L` is infinite.** Suppose `|L| = m < infinity`, and let `y` be any
vertex. By (1b) and (1c), `Stab_y o ⊆ N_Delta o = L`, and
`Stab_o y ⊆ N_Delta y`, which has size `m`. So both orbit sizes lie in
`[1,m]`, and `Delta(o,y) in [1/m, m]` for every `y`. But by (1d) and (1a),
`Delta(o, gamma^n o) = delta(gamma)^n` is unbounded in `n`, for `n` of one
sign. This is a contradiction. ∎

## Part 2. The fibre kernel and its twisted symmetry

**(2a) Kernel.** Let `Delta(o,x) = a`, and choose `gamma` with `gamma o = x`,
so `delta(gamma) = a`. By (1a), `Delta(o, gamma z) = a Delta(o,z)`, and
`gamma` preserves `tau_p`. So

```text
sum_(y in L_b) tau_p(x,y) = sum_(z : Delta(o,gamma z) = b) tau_p(o,z) = sum_(z in L_(b/a)) tau_p(o,z) = sigma_p(b/a).
```

Grouping `z` by level, `sum_(y in L_b) T_p^m(x,y) = sigma_p^(*m)(b/a)` for
every `m >= 1`, by induction:

```text
sum_(y in L_b) T^m(x,y) = sum_c sum_(z in L_c) tau(x,z) sigma^(*(m-1))(b/c) = sum_c sigma(c/a) sigma^(*(m-1))(b/c).
```

Here `(f*g)(d) = sum_e f(e) g(d/e)` on the abelian group `D`. With `x = o`
and `b = 1` this gives `chi^(L,m)_p = sigma_p^(*m)(1)`, and with `m = 1`,
`b = 1` it gives `E_p|K_o ∩ L| = sigma_p(1)`.

**(2b) Twisted symmetry.** Fix `c in D` and let
`F(x,y) = tau_p(x,y) 1[Delta(x,y) = c]`, which is diagonally invariant. The
tilted mass-transport principle at `x = o` gives
`sigma_p(c) = sum_v tau_p(v,o) 1[Delta(v,o) = c] Delta(o,v)`. Now use
`tau_p(v,o) = tau_p(o,v)` and `Delta(v,o) = Delta(o,v)^(-1)`. On the support,
`Delta(o,v) = c^(-1)`, so `sigma_p(c) = c^(-1) sigma_p(c^(-1))`, that is,
`sigma_p(c^(-1)) = c sigma_p(c)`. Then `s_p(c) = c^(1/2) sigma_p(c)`
satisfies `s_p(c^(-1)) = c^(-1/2) c sigma_p(c) = s_p(c)`. Finally,
`sum_c s_p(c) = sum_y tau_p(o,y) Delta(o,y)^(1/2) = chi_(p,1/2)`. ∎

## Part 3. `||S_p|| = chi_p`

Here `||S_p||` is the supremum of `<g, S_p h>` over finitely supported
`g,h >= 0` with unit `l2` norm, as in Step 0 of
`fpbs-quotient-l2-threshold-sandwich-proof`. Note `sum_c sigma_p(c) = chi_p`.

- **Upper bound (Schur test).** Every row sum `sum_b sigma(b/a)` and every
  column sum `sum_a sigma(b/a)` equals `chi_p`. So
  `<g, S h> <= chi_p ||g|| ||h||`. The case `chi_p = infinity` is trivial.
- **Lower bound (Folner).** `D` is countable abelian, so it has Folner sets
  `F_n` with `|F_n ∩ F_n d| / |F_n| -> 1` for each `d in D`. Take
  `g = h = 1_(F_n)/|F_n|^(1/2)`. Then
  `<g, S h> = sum_d sigma(d) |{a in F_n : a d in F_n}| / |F_n|`. By Fatou
  this tends to at least `sum_d sigma(d) = chi_p` as `n -> infinity`.

So `||S_p|| = chi_p` in `[0,infinity]`, and `p^(l2)(L) = p_T`. Since
`chi_p < infinity` forces `|K_o| < infinity` a.s., `p_T <= p_c(G)`. ∎

## Part 4. The chain

- `p^(l2)(L) = p_T <= p_c(G)`: Part 3.
- `p_c(G) < p_t`: `thm:pcpt` with `lambda = 1/2`, since
  `p_c(G,Gamma,1/2) = p_t`.
- `p_t <= p^(diag)(L)`: cut `T^m(o,y)` into its chain sum and use the cocycle
  identity `Delta(o,y)^(1/2) = prod_i Delta(z_i, z_(i+1))^(1/2)`, where
  `z_0 = o` and `z_m = y`. Summing `z_m, z_(m-1), ..., z_1` in turn, and using
  base-point independence of `chi_(p,1/2)(v)` at each step, gives

  ```text
  chi^(L,m)_p = sum_(y in L) T^m(o,y) <= sum_y T^m(o,y) Delta(o,y)^(1/2) = chi_(p,1/2)^m .
  ```

  The first inequality holds because `Delta(o,y) = 1` on `L`. So the diagonal
  rate is at most `chi_(p,1/2)`. That is finite for `p < p_t`, since
  `chi_(p,1/2)` is nondecreasing in `p`.
- `p^(diag)(L) <= p_c(L;G)`: `T^m(o,y) >= tau(o,o)^(m-1) tau(o,y) = tau(o,y)`,
  so `chi^(L,m)_p >= chi^(L,1)_p = E_p|K_o ∩ L|`. If that is infinite, every
  `chi^(L,m)_p` is infinite.
- For `p in (p_c, p_t)`:
  - `E_p|K_o ∩ L| < infinity`, so a.s. `K_o ∩ L` is finite. The same holds at
    each vertex `x` and its level set `L(x) = N_Delta x`, by transitivity.
    Every cluster `K` and every level set `L_c` meet in some `x`, or not at
    all, and then `K ∩ L_c = K_x ∩ L(x)`. There are countably many vertices,
    so a.s. every cluster meets every level set finitely.
  - `||S_p|| = chi_p = infinity` because `p > p_c >= p_T`, while the diagonal
    rate is at most `chi_(p,1/2) < infinity`. ∎

## Part 5. Trees, explicitly

Let `T = T_k` with `k >= 3`, let `xi` be an end, and let `Gamma = Aut(T)_xi`.
Let `u^+` be the neighbour of `u` on the ray from `u` to `xi`, and let
`h(y) - h(x)` be the Busemann height difference (`+1` per step toward `xi`).

- **Transitive.** If `h(x) = h(y)`, the rays from `x` and `y` to `xi` merge
  at a vertex `w` at the same distance `n` from both. Map the segment `[x,w]`
  onto `[y,w]` and fix the ray from `w` to `xi`. Every branch hanging off
  these paths is a rooted `(k-1)`-ary tree, so the map extends to an
  automorphism fixing `xi`. Heights are changed by the translation of length
  1 along any bi-infinite geodesic with one end `xi`, and this also extends to
  an automorphism fixing `xi`.
- **Modular function.** `Gamma_(o^+)` fixes the ray from `o^+` to `xi`, and it
  permutes the `k-1` other neighbours of `o^+` transitively, by swapping
  isomorphic branches. So `|Stab_(o^+) o| = k-1`. `Gamma_o` fixes the ray from
  `o`, which contains `o^+`, so `|Stab_o o^+| = 1`. Hence
  `Delta(u,u^+) = k-1` for every `u`, by transitivity and invariance, and by
  the cocycle identity along paths, `Delta(o,y) = (k-1)^(h(y)-h(o))`. So
  `D = (k-1)^Z` and `L` is the horocycle of `o`.
- **Counting.** A vertex `y` is reached by `a >= 0` steps toward `xi` and
  then `b >= 0` steps away from it, with `d(o,y) = a+b` and
  `h(y) - h(o) = a - b`. The number of such `y` is:
  - `(k-1)^b` if `a = 0`;
  - `1` if `a >= 1` and `b = 0`;
  - `(k-2)(k-1)^(b-1)` if `a, b >= 1`.

  Also `tau_p(o,y) = p^(a+b)`.
- **`p_c(L;T) = 1/sqrt(k-1)`.** The horocycle is `a = b`, so
  `E_p|K_o ∩ L| = 1 + sum_(n>=1) (k-2)(k-1)^(n-1) p^(2n)`. This is finite iff
  `(k-1) p^2 < 1`.
- **`p_t = 1/sqrt(k-1)`.** Each term is at most `p^(a+b) (k-1)^b (k-1)^((a-b)/2) = (p sqrt(k-1))^(a+b)`,
  and at least `((k-2)/(k-1))` times that. So
  `chi_(p,1/2) = sum_y p^(a+b) (k-1)^((a-b)/2)` is finite iff `p sqrt(k-1) < 1`.
- **`p^(l2)(L) = p_T = 1/(k-1) = p_c(T)`.** `chi_p = 1 + sum_(n>=1) k (k-1)^(n-1) p^n`
  is finite iff `p < 1/(k-1)`, and `p_c(T) = 1/(k-1)` is classical.
- **`p^(diag)(L) = 1/sqrt(k-1)`.** Part 4 gives
  `p_t <= p^(diag)(L) <= p_c(L;T)`, and both ends equal `1/sqrt(k-1)`.
  Only the elementary bounds of Part 4 are used, with no import.
- **`p_u(T) = 1`** is classical.
- **Random walk.** Under simple random walk the height moves `+1` with
  probability `1/k` and `-1` with probability `(k-1)/k`. So
  `P(h(X_(2n)) = h(o)) = C(2n,n) ((k-1)/k^2)^n`, whose `2n`-th root tends to
  `2 sqrt(k-1)/k < 1`. ∎
