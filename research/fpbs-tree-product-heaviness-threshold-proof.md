---
rg: 2
id: fpbs-tree-product-heaviness-threshold-proof
kind: route
title: Slabs of a tree product are disjoint finite unions of fibres, so Timar's slab theorem and a Harris bound put fibre-infinite clusters above p_h, and fibre-infinite clusters are heavy
target: fpbs-tree-product-relative-threshold-is-heaviness-threshold
requires:
  - fpbs-hp-relative-sharpness
  - fpbs-timar-infinitely-many-heavy-clusters-percolate-in-a-slab
---

Complete written proof. Notation is as in the target. `P = P_p` is Bernoulli
bond percolation on `G`, `K_x` is the open cluster of `x`, and `o = (1,1)`.
Write `pi(v,x) = v` for the projection to the tree.

**Step 0 (the two forms of the relative threshold agree).** Let
`q_HP = inf{p : a.s. some cluster K has |K ∩ N| = infinity}`.

- If `p < q_HP`, then `fpbs-hp-relative-sharpness` gives an exponential tail
  for `|K_o ∩ N|`, so `E_p|K_o ∩ N| < infinity`. Hence `q_HP <= p_c(N;G)`.
- If `p > q_HP`, then by monotone coupling a.s. some cluster meets `N`
  infinitely. `N` is countable, so some `y in N` has
  `P(|K_y ∩ N| = infinity) > 0`. Left multiplication by `y^(-1)` is an
  automorphism of `G` that maps `N` onto `N` and `y` to `o`. So
  `P(|K_o ∩ N| = infinity) > 0` and `E_p|K_o ∩ N| = infinity`, which gives
  `p >= p_c(N;G)`. Hence `p_c(N;G) <= q_HP`.

**Step 1 (the modular function and slabs).** Let `l : Lambda -> Z` be a
horocycle level function for `xi`. Each vertex `v` has exactly one neighbour
`v^+` (its parent, towards `xi`) with `l(v^+) = l(v) - 1`, and its other
`k - 1` neighbours have level `l(v) + 1`.

- In `Aut_xi(T)`, the stabiliser of `v^+` permutes the `k - 1` children of
  `v^+` transitively, and the stabiliser of `v` fixes `v^+`. So
  `Delta_T(v,v^+) = (k-1)/1 = k-1`. By the cocycle identity along tree
  geodesics, `Delta_T(v,w) = (k-1)^(l(v) - l(w))`.
- `H_grp` acts freely, so `Stab_(Gamma_xi)(v,x) = Stab_(Aut_xi T)(v) x {1}`,
  and `Delta_G((v,x),(w,y)) = Delta_T(v,w)`.
- Hence every slab `{u : e^s <= Delta_G(z,u) <= e^t}` with `s < t` has the
  form `S = L x H_grp`, where `L = {v : a <= l(v) <= b}` for integers `a, b`
  (possibly empty).
- Every fibre `F_v` lies in a slab, since `Delta_G` is identically 1 on `F_v`.

**Step 2 (slab components are finite unions of fibres).**

- Every `u in L` has a unique ancestor `w(u)` at level `a`. For `u, u' in L`,
  the tree geodesic from `u` to `u'` runs up to their meet and back down.
  It stays in `L` iff the meet has level `>= a`, i.e. iff `w(u) = w(u')`.
- So the components of `T[L]` are the sets
  `D_w = {descendants of w of depth <= b - a}` with `l(w) = a`. Each has
  `|D_w| = sum_(j=0)^(b-a) (k-1)^j < infinity`.
- The subgraph of `G = T x H` induced on `S = L x H_grp` is `T[L] x H`,
  because both kinds of product edge have both ends in `S` iff both tree
  coordinates are in `L`. `H` is connected, so its components are the sets
  `D_w x H_grp`.
- Hence a connected infinite subgraph of `G[S]` lies in some `D_w x H_grp`,
  a union of the finitely many fibres `F_v` with `v in D_w`. By pigeonhole it
  meets one of them in an infinite set.

**Step 3 (`p_h <= p_c(N;G)`).**

- Let `p > p_c(N;G)`, and pick `p'` with `p_c(N;G) < p' < p`. By Step 0,
  `p' > q_HP`, so at `p` a.s. some cluster `K` has `|K ∩ N| = infinity`.
- `Delta_G(o,y) = 1` for `y in N = F_1`, so
  `sum_(y in K) Delta_G(o,y) >= |K ∩ N| = infinity`, and `K` is heavy.
- So `G[p]` has a heavy cluster a.s. for every `p > p_c(N;G)`, i.e.
  `p_h <= p_c(N;G)`.

**Step 4 (the number of heavy clusters is a.s. constant, in `{0,1,infinity}`).**
Let `N_h(omega)` be the number of heavy clusters. It is measurable, since
heaviness of `K_x` is a countable-sum condition and there are countably many
`x`. `Delta_G` is `Gamma_xi`-invariant, so every `gamma in Gamma_xi` maps
heavy clusters of `omega` to heavy clusters of `gamma omega`, and
`N_h(gamma omega) = N_h(omega)`.

- *Ergodicity.* `H_grp <= Gamma_xi` acts freely on edges with infinite
  orbits, so for finite edge sets `E_1, E_2` some `h in H_grp` has
  `h E_2 ∩ E_1 = empty`. Let `A` be an `H_grp`-invariant event and `eps > 0`.
  Choose an event `B` depending on a finite edge set `E_0` with
  `P(A Δ B) < eps`, and `h` with `h E_0 ∩ E_0 = empty`. Then `B` and `hB`
  are independent, and `hA = A`. So
  `|P(A) - P(B)^2| = |P(A ∩ hA) - P(B ∩ hB)| < 2 eps`, hence
  `|P(A) - P(A)^2| < 4 eps`. So `P(A) in {0,1}`, and `N_h` is a.s. equal to
  a constant `n in {0,1,2,...} ∪ {infinity}`.
- *Not in `[2, infinity)`.* Suppose `2 <= n < infinity`. Let `B_R` be the
  ball of radius `R` about `o`, with finite edge set `E_R`, and `A_R` the
  event that all `n` heavy clusters meet `B_R`. `A_R` increases to a full
  event, so `P(A_R) > 0` for some `R`. Let `phi(omega)` be `omega` with all
  edges of `E_R` opened. By insertion tolerance,
  `P(phi(A_R)) >= p^(|E_R|) P(A_R) > 0`. The clusters of `phi(omega)` are
  the cluster containing `B_R` (the union of `B_R` and the finitely many
  clusters of `omega` meeting `B_R`) and the clusters of `omega` that miss
  `B_R`, unchanged. On `A_R` the first is heavy, since it contains the `n`
  heavy clusters, and the others are light, since every heavy cluster of
  `omega` meets `B_R`. So `N_h = 1` on `phi(A_R)`, an event of positive
  probability, contradicting `N_h = n` a.s.

**Step 5 (`p_c(N;G) <= p_h`).** Let `p > p_h`. The event "some cluster is
heavy" is increasing, since a superset of a heavy set is heavy. So by
monotone coupling `G[p]` has a heavy cluster a.s., and by Step 4 either
`N_h = 1` a.s. or `N_h = infinity` a.s.

- *Case `N_h = 1`.* For each `x`, `A_x = {K_x is heavy}` is increasing,
  since opening edges only enlarges `K_x`. `theta := P(A_x)` does not depend
  on `x`, by transitivity of `Gamma_xi`. And `theta > 0`, because
  `sum_x P(A_x) >= P(some cluster is heavy) = 1`. For `x in N`, Harris gives
  `P(A_o ∩ A_x) >= theta^2`. On `{N_h = 1}` the event `A_o ∩ A_x` forces
  `o <-> x`. So `tau_p(o,x) >= theta^2` for every `x in N`. `N` is
  infinite, so `E_p|K_o ∩ N| = infinity`.
- *Case `N_h = infinity`.* `Gamma_xi` is a transitive nonunimodular subgroup
  of `Aut(G)`, so
  `fpbs-timar-infinitely-many-heavy-clusters-percolate-in-a-slab` gives a
  slab `S` whose open subgraph has an infinite cluster `C` a.s.
  - By Steps 1 and 2, `C` meets some fibre `F_v` in an infinite set, and so
    does the cluster `K ⊇ C` of `G[p]`.
  - So a.s. some `x` has `|K_x ∩ F_(pi x)| = infinity`. By countable
    additivity some `x` has `P(|K_x ∩ F_(pi x)| = infinity) > 0`.
  - Choose `gamma in Gamma_xi` with `gamma x = o`. `gamma` acts
    coordinatewise, so it maps `F_(pi x)` onto `F_1 = N`. Bernoulli
    percolation is `Aut(G)`-invariant. Hence `P(|K_o ∩ N| = infinity) > 0`,
    and `E_p|K_o ∩ N| = infinity`.

In both cases `p >= p_c(N;G)`. Since `p > p_h` was arbitrary,
`p_c(N;G) <= p_h`. With Step 3, `p_c(N;G) = p_h(G,Gamma_xi)`. ∎

**Remarks.**

- Infiniteness of `H_grp` is used only in the case `N_h = 1`.
- The only external inputs are HP relative sharpness (Step 0, used in
  Step 3) and Timar's slab theorem (Step 5). The proof uses neither Timar's
  Lemma 5.2 nor any property of `p_t`.
- Step 2 is where the product structure enters. For a general nonunimodular
  pair, slab components need not be finite unions of fibres of any subgroup.
