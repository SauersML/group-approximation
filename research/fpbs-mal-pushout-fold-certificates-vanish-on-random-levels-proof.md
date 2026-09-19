---
rg: 2
id: fpbs-mal-pushout-fold-certificates-vanish-on-random-levels-proof
kind: route
title: Cone off the K-Schreier graph inside the level graph to get the triangle presentation, count S-connections that are trivial on K-edges, and bound the first moment on random levels by subadditivity of entropy
target: fpbs-mal-pushout-fold-certificates-vanish-on-random-levels
requires:
  - fpbs-mal-modp-promotion-certificates-are-fox-annihilators
artifacts:
  - experiments/fpbs-pushout-fold-group-2026-09-17/foldgroup.py
  - experiments/fpbs-pushout-fold-group-2026-09-17/verify_pushout.py
  - experiments/fpbs-pushout-fold-group-2026-09-17/small_regular_out.txt
  - experiments/fpbs-pushout-fold-group-2026-09-17/random_means_out.txt
  - experiments/fpbs-pushout-fold-group-2026-09-17/random_means_abelian_out.txt
---

# Proofs

## 0. Conventions

- `L = F(a, b)`, `c = b a b^-2`, `K = <a, c>`.
- `{b, c}` is a free basis of `L`: `<b, c>` contains `a = b^-1 c b^2`, and a
  generating pair of `F_2` is a basis (Hopfian). Likewise `{c, cb}`, since
  `b = c^-1 (cb)`.
- Actions are on the right. `Gamma` is the Schreier graph of the level `V`
  for the basis `{b, c}`, with an edge `v -> v.b` and an edge `v -> v.c` for
  each `v`. So `N = pi_1(Gamma, v0)`, with the loop label map an isomorphism,
  because `Gamma` covers the rose of `{b, c}`.
- `K` is free on `a, c`, since `phi : a -> a, b -> c` is injective.
  `Y_K` is the Schreier graph of `K` on `V` for `{a, c}`. The map
  `iota : Y_K -> Gamma` sends the `c`-edge at `v` to the `c`-edge at `v`, and
  the `a`-edge at `v` to the edge path reading `b^-1 c b b` from `v`.
  On the component of `v0`, `iota_*` is the inclusion `K cap N -> N`.
- An *S-connection* on a graph is a map `phi` from edges to `S`. Holonomy
  along a path is the product of the values, in order, with `phi(e)^-1` for
  an edge traversed backwards. Holonomy of loops at `v0` is a homomorphism
  `pi_1 -> S`.

## 1. Theorem A

Assume `K` is transitive on `V`, so `Y_K` is connected.

1. Form `X_1` from `Gamma` by adding, for each `v`, a new edge `e_v` from `v`
   to `v.a`, and a 2-cell `D_v` whose boundary is `e_v` followed by the
   inverse of the path `b^-1 c b b` from `v`. Each `D_v` collapses onto its
   free face `e_v`, so `X_1` deformation retracts to `Gamma`, and
   `pi_1(X_1, v0) = N`.
2. The subcomplex `Y := (c-edges) u (e_v)` of `X_1` is a copy of `Y_K`, and
   `pi_1(Y, v0) -> pi_1(X_1, v0) = N` is `iota_*`, the inclusion of
   `K cap N`.
3. By van Kampen, attaching the cone on the connected subcomplex `Y` gives
   `pi_1(X_1 u CY) = N / <<K cap N>>^N`.
4. `(X_1, Y)` is a CW pair and `CY` is contractible, so
   `X_1 u CY ~ X_1 / Y`. Since `Y` contains every vertex, `X_1 / Y` has one
   vertex. Its edges are the `b`-edges, written `t_v` for the edge
   `v -> v.b`. Its 2-cells are the images of the `D_v`.
5. The boundary of `D_v`, after the `c`-edges and `e_v` are collapsed, reads
   along `b^-1 c b b` from `v`. The first letter traverses `t_w` backwards,
   where `w = v.b^-1`. The `c`-edge collapses. Then `t_{wc}` and `t_{wcb}`
   are traversed forwards. So the relator is
   `t_w^-1 t_{wc} t_{wcb}`, for every `w` in `V` (as `v` ranges over `V`, so
   does `w`). This gives
   `N / <<K cap N>>^N = < t_w | t_w = t_{wc} t_{wcb} > = P_V`.

Complements.
- **Regular levels.** If `N` is normal, `M := <<K cap N>>^N` is normal in
  `L`. Conjugation by `N` preserves it, and so does conjugation by `K`, which
  preserves `K cap N` and `N`; and `L = K N` by transitivity. Then
  `L/M = L *_K Q` (both are `L` modulo the normal closure of `K cap N`), and
  `L = <b, c>` gives `<Q, b | b alpha b^-2 = gamma>`. `K` maps onto a
  complement of `N/M` isomorphic to `Q`.
- **Triangles.** `t_v` occurs in the relators at `w = v`, `w = v.c^-1` and
  `w = v.b^-1 c^-1`, once each.
- **Relative rank.** If `N = <K cap N, g_1, ..., g_e>`, then the images of the
  `g_i` generate `P_V`, so `d(P_V) <= d(N | K cap N)`.
- **Percolation.** If a subgroup contains two of `t_w, t_{wc}, t_{wcb}`, it
  contains the third. So the `t_v` over a 2-of-3 percolating set generate
  `P_V`, and `d(P_V) <= r(V)`.
- **Abelianization.** The abelianized relation matrix has rows
  `e_w - e_{wc} - e_{wcb}`. It is the transpose of right multiplication by
  `u = 1 - c - cb` on `Z[V]`, since the coefficient of `w` in `y.u` is
  `y_w - y_{w c^-1} - y_{w b^-1 c^-1}`. The two have the same Smith form. In
  particular `log_p Z_{F_p}(V) = k_u(V)` over `F_p`.

## 2. Theorem B

Let `V` be any level (any number `t` of `K`-orbits), `Y` a generating graph with
extra edges `i = 1..E` from `v_i` to `v_i.l_i`, and `S` a finite group.

**Step 1 (colourings are flat connections).** Let `Z'` be the set of
`S`-connections `phi` on `Gamma` that satisfy two conditions:
- `phi` is 1 on every `c`-edge;
- the holonomy along the path reading `a = b^-1 c b b` from every `v` is 1.

Given `s`, put `phi(v -> v.b) = s_v` and `phi = 1` on `c`-edges. As in §1.5,
the `a`-path holonomy from `v = w.b` is `s_w^-1 s_{wc} s_{wcb}`. So
`s -> phi` is a bijection from the `S`-fold colourings onto `Z'`, and
`|Z'| = Z_S(V)`.

**Step 2 (holonomy map).** For `phi` in `Z'`, let `h_i(phi)` be the holonomy of
`phi` along the `Gamma`-path from `v_i` that reads `l_i`, written in `b, c`.
This is well defined because free reduction only cancels backtracks. Put
`h = (h_i) : Z' -> S^E`.

**Step 3 (fibres lie in gauge orbits).** Let `rho_phi : N -> S` be the holonomy
of loops at `v0`.
- Take a closed path in `Y` at `v0` with label `l`. The value of `rho_phi(l)`
  is the ordered product of edge contributions. `c`-edges and `a`-edges
  contribute 1 (Step 1). Extra edge `i` contributes `h_i(phi)^{+-1}`.
- The loop labels generate `N`. So `rho_phi` is determined by `h(phi)`.
- On the connected graph `Gamma`, `rho_phi = rho_phi'` iff `phi' = g.phi`,
  where `(g.phi)(x -> y) = g_x phi(e) g_y^-1`, for a unique `g : V -> S` with
  `g_{v0} = 1`. This gauge action is free: propagate `g_{v0} = 1` along edges.
- Suppose `phi` and `phi'` are both in `Z'`.
  - On `c`-edges, `g_x g_{xc}^-1 = 1`.
  - On `a`-paths, `g_v g_{va}^-1 = 1`.
  - So `g` is constant on `K`-orbits.
- Let `G_t` be the set of `g : V -> S` that are constant on `K`-orbits with
  `g_{v0} = 1`. Then `G_t` is isomorphic to `S^(t-1)` and preserves `Z'`. It
  acts freely on `Z'`, and each fibre of `h` lies in one `G_t`-orbit.

**Step 4 (count).**
- `G_t` acts on `S^E` by `h_i -> g_{v_i} h_i g_{v_i l_i}^-1`, and `h` is
  equivariant. By Step 3 the induced map `Z'/G_t -> S^E/G_t` is injective.
- Contract each `K`-orbit of `Y_K` to a point. The extra edges then form a
  connected multigraph on `t` vertices, because `Y` is connected.
- Pick a spanning tree `T` in it, with `t - 1` edges, rooted at the orbit of
  `v0`. Given any values on the edges of `T`, solving outward from the root
  (where `g = 1`) gives exactly one `g` in `G_t` that moves a given point to
  them. So `G_t` acts simply transitively on the `T`-coordinates.
- Hence every orbit in `S^E` contains exactly one point with all
  `T`-coordinates equal to 1, and `|S^E / G_t| = |S|^(E - t + 1)`.
- Therefore

```text
Z_S(V) = |Z'| = |G_t| |Z'/G_t| <= |S|^(t-1) |S|^(E-t+1) = |S|^E .  []
```

For `S = F_p`, `Z = p^(k_u)` by §1, so this recovers `E >= k_u`.

**Corollary (witnesses).** For a free profinite witness `X = lim V_m`,

```text
Q_0(X) >= limsup_m log_|S| Z_S(V_m) / |V_m| .
```

*Proof.* Repeat the proof of Theorem 2 of
`fpbs-mal-modp-promotion-certificates-are-fox-annihilators`. Its steps 1-3
build, for `m >= m_0`, a generating graph on `V_m` with
`E_m < (eps + delta)|V_m|` extra edges. They never use the field. Step 4 uses
only `E_m >= k_u(V_m)`; replace it by Theorem B. []

## 3. Theorem C

Let `b, c` be independent uniform permutations of `[n]`, and write
`X v = v.c` and `Y v = v.cb`.

**Step 1 (independence).** For fixed `c`, the map `b -> cb` is a bijection of
`Sym(n)`. So `(c, cb)` is uniform on `Sym(n)^2`, and `X`, `Y` are independent
and uniform.

**Step 2 (exact first moment).** Let `N_F` be the number of `s` in `S^n` with
`s_v = F(s_{Xv}, s_{Yv})` for all `v`.
- Fix `s` of type `(n_g)`, where `n_g = #{v : s_v = g}`.
- `sigma = s o X` and `tau = s o Y` are independent. Each is uniform among the
  `n! / prod_g n_g!` arrangements of type `(n_g)`.
- Swap the sums over `s` and over `(sigma, tau)`. Since `s = F(sigma, tau)` is
  determined, `E N_F` is a sum over pairs `(sigma, tau)` in which `sigma`,
  `tau` and `F(sigma, tau)` all have the same type.
- Group the pairs by their joint type `m_{hk} = #{v : sigma_v = h, tau_v = k}`.
  Call `m` *admissible* when its row sums and column sums both equal some
  `(n_g)` and `sum_{F(h,k) = g} m_{hk} = n_g`. Then

```text
E N_F = sum_{admissible m} ( n! / prod_{h,k} m_{hk}! ) ( prod_g n_g! / n! )^2 .
```

**Step 3 (each term is polynomial).** Write `H` for Shannon entropy and `m/n`,
`p = (n_g/n)` for the normalised tables. Two standard type-class bounds hold:
- `n! / prod m_{hk}! <= e^{n H(m/n)}`;
- `n! / prod n_g! >= (n+1)^{-|S|} e^{n H(p)}`.

So each term is at most `(n+1)^{2|S|} e^{n (H(m/n) - 2 H(p))}`. Both marginals
of `m/n` equal `p`, so subadditivity gives `H(m/n) <= 2 H(p)`. Each term is
therefore at most `(n+1)^{2|S|}`.

**Step 4 (sum and Markov).**
- There are at most `(n+1)^{|S|^2}` tables with entries in `[0, n]`. So
  `E N_F <= (n+1)^{|S|^2 + 2|S|}`.
- By Markov, `P(N_F >= (n+1)^{|S|^2 + 2|S| + 1}) <= 1/(n+1)`.
- For a group `S` with `F(h,k) = hk`, `N_F = Z_S(V_n)`. For `S = F_p` with
  `F = +`, `N_F = p^(k_u(V_n))`. []

**Conditioning.** If `P(A) >= delta`, then
`P(bad | A) <= P(bad) / delta <= 1 / (delta (n+1))`.

**Scope.** Every bound above holds for each fixed `S`, for example for `S` in
a fixed finite list. A union over all groups of order `n^{o(1)}` would need a
larger Markov threshold. It is not claimed.

## 4. Computations (evidence, not part of the proofs)

All scripts are in `experiments/fpbs-pushout-fold-group-2026-09-17/`.

- `verify_pushout.py` checks Theorem A. It counts `S`-connections on `Gamma`
  that are trivial on a spanning tree and have trivial holonomy on the
  `K`-graph, and compares with the colouring count `Z_S`. There were 120
  (level, `S`) cases and 0 mismatches.
- `random_means.py` measures the mean of `Z_S` on uniformly random levels.
  - `random_means_out.txt`: `n` = 8, 16, 32, for `C_2`, `C_3` and `S_3`.
  - `random_means_abelian_out.txt`: `n` = 64, 128, 256, for `C_2` and `C_3`,
    by rank over `F_p`.
  - The mean is flat in `n`. This is far below the bound of Theorem C.
- `small_regular.py` (output `small_regular_out.txt`) looks at small Cayley
  levels. It includes an `A_4` level on which `P_V` is perfect and maps onto
  `A_5`.
- `regular_out.txt` covers the PSL2 Cayley levels.
- `random_out.txt` is an early partial run.
