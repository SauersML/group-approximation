# Replica meets see amenable free factors, not uniqueness: [cap_inf] is false

Date: 2026-09-19. Lane: swarm-0917 w14-bs-follow.
Claim: `fpbs-replica-meet-cap-inf-fails-free-products`.
Route: `fpbs-replica-meet-cap-inf-fails-free-products-proof`.

Notation is that of `replica-meet-threshold-2026-09-18.md` (the "meet
artifact"). `K^i(o)` is the open cluster of `o` in the `i`-th of `k`
independent Bernoulli(`p`) configurations `omega^1, ..., omega^k`,
`M_k(o) = K^1(o) ∩ ... ∩ K^k(o)`, and

```text
p_cap^(k) = sup{ p : |M_k(o)| < infinity a.s. },   p_cap^(infty) = sup_k p_cap^(k).
```

Section 4 of the meet artifact asks:

> **Question [cap_inf].** Is `p_cap^(infty) = p_u` on every nonamenable Cayley
> graph? It holds on `T_d` (item 5).

and calls a positive answer "a replica characterisation of nonuniqueness".
The answer is **no**.

## 1. Statement

**Theorem.** Let `A` be an infinite, finitely generated, amenable group with
finite symmetric generating set `S_A`, and let `L = Cay(A, S_A)`. Assume
`p_c(L) < 1`. Let `Gamma = A * Z/2 = A * <t>` and
`G = Cay(Gamma, S_A ∪ {t})` (right Cayley graph, edges `{g, gs}`). Then:

1. `Gamma` is nonamenable;
2. `p_c(G) <= p_c(L) < 1 = p_u(G)`;
3. `p_cap^(k)(G) <= p_c(L)` for every `k >= 1`.

Hence `p_k(G) <= p_cap^(k)(G) <= p_c(L)` for every `k`, and

```text
p_cap^(infty)(G) <= p_c(L) < 1 = p_u(G).
```

**Concrete instance.** `A = Z^2`, `S_A = {a^±1, b^±1}`, so `L` is the square
lattice and `G = Cay(Z^2 * Z/2, {a^±1, b^±1, t})` is 5-regular. The Peierls
bound (Section 3, script
`experiments/replica-meet-free-product-2026-09-17/peierls_bound.py`) gives
`p_c(L) <= 9/10`, so

```text
p_cap^(infty)(G) <= 9/10 < 1 = p_u(G),
```

a gap of at least `1/10` that no number of replicas closes. Kesten's theorem
`p_c(Z^2) = 1/2` (cited elsewhere in the graph, for example in
`fpbs-lossless-move-comparison-fails-marginal-transfer-proof`) improves this
to `p_cap^(infty)(G) <= 1/2`. That improvement is a remark and is not used.

## 2. Proof

### 2.0 Structure of `G`

Every element of `Gamma` has a unique reduced normal form, an alternating word
in nontrivial elements of `A` and the letter `t` (normal form theorem for free
products).

- For each coset `gA`, the edges `{ga, gas}` with `s in S_A` stay inside `gA`,
  and `a ↦ ga` identifies the subgraph induced on `gA` with `L`. Call it the
  *plane* `P_(gA)`. The plane through `o = e` is `P_A`, which is `L` itself.
- Each vertex `g` has exactly one `t`-edge, `{g, gt}`.
- Contract every plane to a point. The result `T` has vertex set `Gamma/A`
  and one edge `{gaA, gatA}` for each `t`-edge `{ga, gat}`. The cosets
  `gatA`, for `a in A`, are pairwise distinct: `gatA = ga'tA` forces
  `t a^(-1) a' t in A`, which by the normal form forces `a = a'`. A cycle in
  `T` would give a nonempty reduced word equal to `e`. So `T` is a tree
  without multiple edges (the Bass–Serre tree).
- Planes are connected and each `t`-edge maps to an edge of the tree `T`, so
  **every `t`-edge of `G` is a bridge**. Every other edge lies in one plane.

**Nonamenability.** An exponent-2 group is abelian, and a finitely generated
abelian exponent-2 group is finite. So `A` has an element `a` of order
`m >= 3` (possibly `m = infinity`). By the normal form,
`<a, tat> = <a> * t<a>t` is a free product of two cyclic groups of order `m`.
For `m = infinity` it is `F_2`. For finite `m >= 3`, the kernel of
`Z/m * Z/m -> Z/m x Z/m` is free of rank `(m-1)^2 >= 4` (Kurosh). Either way
`Gamma` contains a nonabelian free group and is nonamenable. For `A = Z^2`,
`a` and `tat` directly generate `F_2`.

### 2.1 `p_u(G) = 1`

`p_c(G) <= p_c(L) < 1`, since `L = P_A` is a subgraph of `G`.

Fix `p in (p_c(G), 1)`. Let `e = {o, t}`. Removing the bridge `e` leaves two
components: `W_o` containing `o` and `W_t` containing `t`. Every edge other
than `e` has both endpoints in one of them. Left multiplication `lambda_t`
by `t` is an automorphism of `G` that swaps `o` and `t` and fixes `e`, so it
swaps `W_o` and `W_t` and preserves `P_p`. Define

```text
E_1 = { o is joined to infinity by an open path inside W_o },
E_2 = { t is joined to infinity by an open path inside W_t },
E_3 = { e is closed }.
```

- `P(E_1) = P(E_2) =: alpha`, by `lambda_t`.
- `alpha > 0`. Take a self-avoiding infinite open path from `o`. If it avoids
  `e`, it stays in `W_o`, because leaving `W_o` means crossing `e`. If it uses
  `e`, then `e` is its first edge: it must stand at `o` to cross, and a
  self-avoiding path is at `o` only at time 0. The rest is then a
  self-avoiding infinite open path from `t` inside `W_t`. So
  `theta(p) <= P(E_1) + P(E_2) = 2 alpha`, and `theta(p) > 0` for
  `p > p_c(G)` on the transitive graph `G`.
- `E_1`, `E_2` and `E_3` are determined by pairwise disjoint edge sets, so
  they are independent.
- On `E_1 ∩ E_2 ∩ E_3`, the clusters of `o` and `t` are both infinite. They
  are distinct, because every path from `o` to `t` uses the closed bridge `e`.

So `P_p(N_infinity >= 2) >= alpha^2 (1 - p) > 0`. By the trichotomy
(`fpbs-cluster-count-trichotomy`, item 1), `N_infinity(p) = +infinity` a.s.
for every `p in (p_c(G), 1)`.

If `p_u(G) < 1`, item 2 of the same import would give `N_infinity(p) = 1` for
every `p in (max(p_u, p_c(G)), 1)`, which is a contradiction. Hence
`p_u(G) = 1`.

### 2.2 `p_cap^(k)(G) <= p_c(L)`

Fix `k >= 1` and `p in (p_c(L), 1)`. Restricted to the edges of the plane
`P_A = L`, each `omega^i` is Bernoulli(`p`) percolation on `L`, and the `k`
restrictions are independent.

- **One infinite plane cluster per replica.** Because `p > p_c(L)`, `L` has an
  infinite `omega^i`-cluster with positive probability, hence a.s. by
  Kolmogorov's 0-1 law. Apply `fpbs-hp-relative-burton-keane` to the Cayley
  graph `L` of `A` with `H = A` (amenable). An `A`-infinite cluster is just an
  infinite cluster, so there is at most one. Call the unique infinite cluster
  of `omega^i|_L` by the name `C_i ⊆ A`.
- **The meet of the plane clusters.** Let `D = C_1 ∩ ... ∩ C_k ⊆ A`.
  - Left multiplication by `A` acts transitively on `L` by automorphisms,
    preserves the joint law of `(omega^i|_L)_i`, and maps `C_i` to the
    corresponding cluster of the translated configuration. So the law of `D`
    is invariant under a transitive group action.
  - `o in C_i` if and only if the `L`-cluster of `o` in `omega^i` is infinite.
    By independence, `P(o in D) = theta_L(p)^k > 0`.
- **`D` is infinite whenever it contains `o`.** This is Lemma 1.1 of the meet
  artifact (route `fpbs-replica-meet-threshold-sandwich-proof`, item 3),
  restated here. By invariance, `P(x in D, |D| = n)` does not depend on
  `x in A`. Summing over `x`,
  `n P(|D| = n) = sum_(x in A) P(x in D, |D| = n)`. The left side is finite
  and `A` is infinite, so `P(o in D, |D| = n) = 0` for every `n`. Hence
  `P(o in D, |D| < infinity) = 0`.
- **`D` lies in the meet.** On `{o in D}`, each `C_i` is a connected set of
  `omega^i`-open edges of `G` that contains `o`, so `C_i ⊆ K^i(o)`. Hence
  `D ⊆ M_k(o)`.

Therefore `P_p^(k)(|M_k(o)| = infinity) >= P(o in D) = theta_L(p)^k > 0`.
Under the monotone coupling, `M_k(o)` is nondecreasing in each `omega^i`, so
the set `{p : |M_k(o)| < infinity a.s.}` is an initial segment of `[0,1]`.
It misses `p`, so `p_cap^(k)(G) <= p`. Let `p ↓ p_c(L)`.

### 2.3 Conclusion

Combining 2.1 and 2.2, `p_cap^(k)(G) <= p_c(L) < 1 = p_u(G)` for every `k`.
Item 1 of `fpbs-replica-meet-threshold-sandwich` gives `p_k <= p_cap^(k)`, so
`sup_k p_k(G) <= p_c(L)` too. ∎

## 3. Peierls bound for `L = Z^2`

A finite open cluster at `o` in `Z^2` is surrounded by a closed dual circuit.
The number of dual circuits of length `n` that surround `o` is at most
`n * 4 * 3^(n-2) <= 4 n 3^(n-1)`, and `n >= 4`. So

```text
P_p(|C(o)| < infinity) <= sum_(n >= 4) 4 n 3^(n-1) (1-p)^n = 837/12250 ≈ 0.0683   at 1 - p = 1/10.
```

The script evaluates this in exact rational arithmetic, both in closed form and
as a 200-term partial sum. Its output is in `peierls_bound.out`. So
`theta_(Z^2)(9/10) >= 0.93 > 0` and `p_c(Z^2) <= 9/10`.

## 4. What this changes

1. **[cap_inf] is false.** The meet thresholds are capped by thick amenable
   pieces, not by uniqueness. On `T_d` (a Cayley graph of a virtually free
   group) the infinite amenable subgroups are virtually cyclic. A cluster is a
   subtree and meets a geodesic axis in an interval, so their relative
   thresholds are 1. That explains why the tree calibration suggested
   equality.
2. **Kill: equivalence of [cap_fin] and BS through meet thresholds.** A
   positive answer to [cap_inf] would have given BS ⇒ [cap_fin]: if
   `p_cap^(k) ↑ p_u > p_c`, then some `k` has `p_c < p_cap^(k)`. That
   reverse implication cannot come from approximating `p_u` by meet
   thresholds. On `G`, BS holds (Section 5) while every `p_cap^(k)` stays at
   least `1 - p_c(L)` below `p_u`. Any proof of [cap_fin] must produce
   `p_c < p_cap^(k)` inside the window below `p_c(L)`. That window is the
   relative window of the amenable plane, not the nonuniqueness window.
3. **The mechanism, and where it is harmless.** The proof in 2.2 bounds
   `p_cap^(infty)` by the threshold of any amenable *subgraph* `L` that is a
   Cayley graph of a subgroup. The bus lemma of w14-bs-last1
   (`fpbs-soft-collapse-kills-as-replica-meet-arguments`, not in this
   worktree) posts the relative form `p_cap^(k) <= p_c(H;G)` for infinite
   amenable `H`, and the same proof gives it. For an amenable **wq-normal**
   `H`, `fpbs-amenable-wq-normal-pu-is-relative-pc` gives
   `p_c(H;G) = p_u(G)`, so the bound is harmless there. The counterexample
   uses a free factor, which is malnormal and far from wq-normal, and whose
   planes are separated by bridges.

## 5. Consistency checks

- **BS on `G`.** Several standard facts are recalled here and not used in
  the proof:
  - `Z^2` has cost 1 and `Z/2` has cost `1/2`;
  - cost is additive under free products (Gaboriau);
  - so `cost(Z^2 * Z/2) = 3/2 > 1`, and Lyons' cost theorem gives BS.

  BS also follows directly from 2.1: `p_c(G) <= 9/10 < 1 = p_u(G)`. The
  counterexample is consistent with BS and does not touch it.
- **The tree case.** `A = Z` has `p_c(L) = 1`, and the theorem says nothing.
  `Z * Z/2` is virtually free. Whether `p_cap^(infty) = 1` there is not
  settled here.
- **Sandwich.** `p_cap^(k)(G) <= p_c(G)^(1/k)` also holds, but for large `k`
  it is weaker than `p_c(L)`. The amenable-plane bound is uniform in `k`, and
  that uniformity is exactly what kills [cap_inf].

## 6. What is left

- **[cap_inf] for one-ended graphs.** Open. In one-ended groups, amenable
  pieces glued along infinite sets tend to merge clusters. Plausibly
  `p_u <= p_c(H;G)` for many amenable `H` there, but no general statement is
  known here.
- **[cap_fin] on `Z^2 * Z/2`.** A concrete test case. It asks whether
  `p_c(G) < p_cap^(k)(G)` for some `k`, which requires first that
  `p_c(G) < p_c(L)`. That strict inequality is expected, because the trees of
  planes attached through the bridges should enhance, but it is not proved
  here. `G` is relatively hyperbolic but not hyperbolic, so the import in
  `fpbs-hyperbolic-nonunimodular-critical-l2-gap` does not apply as stated.
