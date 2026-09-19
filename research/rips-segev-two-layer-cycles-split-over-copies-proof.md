---
rg: 2
id: rips-segev-two-layer-cycles-split-over-copies-proof
kind: route
title: When u(1) + w(1) = 0 the edge equation X(z b) = -Y(z) closes the a-parts into a finite 1-cycle; relators are closed paths in Gamma, so the cycle is a sum of cycles in copies; a nonzero cycle of a copy passes through a Phi-cycle of at least 42 lines; on a line no other copy's cycle touches, every port is a port of that copy, which the rank-one lemma allows on one row only
target: rips-segev-two-layer-cycles-split-over-copies
requires: [rips-segev-three-copy-configurations-carry-no-zero-divisors, rips-segev-two-copy-configurations-carry-no-zero-divisors, rips-segev-one-copy-configurations-carry-no-zero-divisors]
---

**Conventions.**
- [3C] is `rips-segev-three-copy-no-zero-divisors-proof` (rank-one lemma).
- [2C] is `rips-segev-two-copy-configurations-carry-no-zero-divisors` (two-link lemma).
- [1C] is `rips-segev-one-copy-configurations-carry-no-zero-divisors` (mechanism 1: a coset meets a copy in at
  most one line).
- Chains are finite `k`-linear combinations of oriented edges of `Cay`.  `∂[x -> y] = y - x`.
- A cycle is a chain with `∂ = 0`.  For a subgraph `C`, `Z_1(C)` is the space of cycles supported on edges of `C`.
- Coset coordinates: `T = z_T <a>`, and `z_T a^i` has coordinate `i`.  A chain on the `a`-edges of `T` is written
  as a Laurent series `sum_i phi_i t^i`, where `phi_i` is the coefficient of `[z_T a^i -> z_T a^{i+1}]`.

**Step 0 (`G` reduces to `K`).**
- Write `alpha = sum_r g_r alpha_r`, with `g_r` distinct representatives of left `K`-cosets in `G` and
  `alpha_r in k[K]`.
- Then `alpha (u + w b) = sum_r g_r (alpha_r (u + w b))`, and the summands have disjoint supports.
- So each `alpha_r (u + w b) = 0`, and some `alpha_r != 0`.  From now on everything is in `k[K]`.

**Step 1 (harmonic cycle).**
- *`b`-part.*  Put `c_b = sum_z Y(z) [z -> z b]`.
  - At a vertex `v`, the edge `[v b^{-1} -> v]` contributes `Y(v b^{-1})` and the edge `[v -> v b]` contributes
    `-Y(v)`.
  - The coefficient of `v` in `alpha u + alpha w b = 0` gives `X(v) = -(alpha w b)(v) = -Y(v b^{-1})`.
  - So `(∂ c_b)(v) = -X(v) - Y(v) = -(alpha (u + w))(v)`.
- *`a`-part.*  On a coset `T`, `alpha (u + w)` restricts to `z_T h_T(a)` with `h_T = f_T (u + w)`.
  - For a chain `phi_T` on the `a`-edges of `T`, `(∂ phi_T)(z_T a^i) = phi_{i-1} - phi_i`.  This is the
    coefficient of `t^i` in `(t - 1) phi_T(t)`.
  - So `∂(c_b + sum_T phi_T) = 0` iff `(t - 1) phi_T = h_T` for every `T`.
  - Since `h_T(1) = f_T(1) (u(1) + w(1)) = 0`, `t - 1` divides `h_T` in `k[t^{±1}]`, and
    `phi_T = h_T / (t - 1)` is a Laurent polynomial.
  - Only the finitely many cosets meeting `supp alpha` have `h_T != 0`.
- *Nonzero.*  `Y = alpha w != 0`: on each coset `f_T w = 0` forces `f_T = 0`, since `k[t^{±1}]` is a domain, and
  `alpha != 0`.  So `c` is a finite nonzero cycle whose `b`-coefficients are exactly `Y`.

**Step 2 (splitting).**
- *Relator loops lie in copies.*  Every relator `r` is the label of a closed path `p` in `Gamma`, from a vertex `v`.
  The loop in `Cay` read from `r` at a vertex `x` is `h g(p)` with `h = x g(v)^{-1}`, because `g` preserves labels.
  So that loop lies in the copy `h g(Gamma)`.
- *Loops in `Cay` are sums of relator loops.*  Let `q` be a closed edge path in `Cay`.  Its label equals
  `prod_s y_s r_s^{±1} y_s^{-1}` in the free group `F(a, b)`.
  - The Hurewicz map `pi_1(Cay) -> Z_1(Cay; Z)` is a homomorphism, and conjugating paths cancel.
  - So the cycle of `q` is a sum of `±` cycles of relator loops, each in a copy.
- *All cycles.*  `Z_1(Cay; Z)` is spanned by cycles of closed paths (fundamental cycles of a spanning tree).
  - Also `Z_1(Cay; k) = Z_1(Cay; Z) ⊗ k`, since `C_0 / ∂ C_1` is free abelian for a graph.
  - So every finite `k`-cycle is a finite sum of cycles in copies.
- Grouping the terms of `c` by copy and dropping zero groups gives `c = sum_{i <= N} c_i`, with distinct copies
  `C_i` and `0 != c_i in Z_1(C_i; k)`.  `N >= 1`, since `c != 0`.
- *Uniqueness criterion.*  The coned-off complex `X^` adds to `Cay` a cone on each copy.
  - A relation `sum_i c'_i = 0` with `c'_i in Z_1(C_i)` gives `c'_i = ∂ kappa_i`, with `kappa_i` a 2-chain in the
    cone on `C_i` (cones are contractible).
  - Then `sum_i kappa_i` is a 2-cycle of `X^`.  Distinct cones have disjoint 2-cells, and `X^` has no 3-cells.
  - So `H_2(X^; k) = 0` forces every `kappa_i = 0`, and so every `c'_i = 0`.
  - Conversely, a nonzero 2-cycle `sum kappa_i` gives the nontrivial relation `sum ∂ kappa_i = 0` among copy
    cycles.  Its cone edges cancel copy by copy, so the `∂ kappa_i` are cycles in `C_i`.  They are not all zero,
    since a cone has no nonzero 2-cycle.
  - Nothing below uses uniqueness.

**Step 3 (cycle lines).**
- By `Gr'(1/6)`, each copy `C = h g(Gamma)` is an embedded copy of `Gamma` (Ollivier; Gruber, graphical `C(6)`,
  Lemma 2.15).  So `Z_1(C) = Z_1(Gamma)` along the labelled isomorphism.
- The lines of `Gamma` are finite `a`-paths partitioning `V(Gamma)`, so they form a spanning forest of the
  `a`-edges.  Contracting them gives `Phi`, with lines as vertices and `b`-edges as edges.
- A cycle with zero `b`-part is a cycle on a forest, hence zero.  So the `b`-part of `c_i != 0` is a nonzero cycle
  of `Phi`.
- In the support of a nonzero cycle, no vertex has degree 1.  So the support contains a cycle of `Phi`, whose
  `>= girth(Phi) >= 42` vertices are distinct lines of `Lambda_i`.
- By [1C] mechanism 1, a coset meets `C_i` in at most one line.  So distinct cycle lines lie in distinct cosets.

**Step 4 (untouched lines are pure).**  Let `l` be an untouched cycle line of `C_i`, in the coset `T`.
- On every edge with an endpoint in `T`, `c = c_i`, since the other `c_j` vanish there.
- *Active.*  `c_i` is nonzero on a `b`-edge `e = [y -> y b]` of `C_i` with an endpoint on `l`.  Then `c(e) = Y(y)`
  is nonzero.
  - If `y in T`, then `Q_T != 0`.  If `y b in T`, then `X(y b) = -Y(y) != 0`, so `P_T != 0`.  Either way
    `f_T != 0`.
- *Out-ports.*  Let `z in T` with `Y(z) != 0`.  Then `c([z -> z b]) != 0`, so some `c_j` is nonzero on this edge.
  - The edge has the endpoint `z in T`, so `j = i`, and the edge is a `b`-edge of `C_i`.
  - So `z in C_i ∩ T = l`, and its position on `l` is the source of a `b`-edge of `Gamma`, that is, lies in `Out_l`.
- *In-ports.*  If `X(z) != 0` with `z in T`, then `Y(z b^{-1}) != 0`, and in the same way `z in In_l`.
- Take the start of `l` as base point of `T`.  Then `S_T = supp P_T ∪ supp Q_T ⊆ D_r = {0} ∪ {10^e : 5r-4 <= e <= 5r}`,
  where `r` is the row of `l`.
- *Rows separate.*  The nonzero elements of `D_r - D_r` are `±10^e` and `±(10^e - 10^f)`, with
  `5r-4 <= f < e <= 5r`.
  - In decimal these are `1 0^e` and `9^{e-f} 0^f`.  The string determines `e`, and `e` determines `r`.
  - So `(D_r - D_r) ∩ (D_{r'} - D_{r'}) = {0}` for `r != r'`.
- *At most one row.*  Two untouched cycle lines lie in distinct cosets:
  - for one copy, by Step 3;
  - for two copies, because a cycle line of `C_j` is touched by `c_j`, so it cannot lie in an untouched coset of
    `C_i`.
  - If their rows differed, the rank-one lemma of [3C] would give `u = c w` and `alpha = 0`.
  - So all untouched cycle lines share one row.  Lines of one copy have distinct rows (`phi` is injective), so each
    copy has at most one untouched cycle line.

**Step 5 (reduction).**
- Apply LC to the splitting of Step 2.  Some `C_i` has two untouched cycle lines, which contradicts Step 4.
- Steps 1–4 hold over every field, and Step 0 passes from `k[G]` to `k[K]`.

**Step 6 (`N <= 14`).**
- Suppose a cycle line of `C_i`, in the coset `T`, is touched by `c_j`.  Then `C_j` has an edge with an endpoint
  `y in T`.
- `y` lies on a line of `C_j`, and that line lies in `y <a> = T`.  So `T` is a coset shared by `C_i` and `C_j`.
- By the two-link lemma of [2C], two distinct copies share at most 3 cosets: a bridge is their only link, and
  otherwise `girth(Phi) > 12` bounds the shared cosets by 3.
- Distinct cycle lines lie in distinct cosets, so at most `3(N - 1)` cycle lines of `C_i` are touched.
- For `N <= 14` that is at most 39.  So at least 3 of the `>= 42` cycle lines are untouched, and LC holds.
- The same count applies to any family with at most 9 shared cosets per copy, such as the star family of
  `rips-segev-coefficient-free-extremal-copy-lemma-fails`: at least 33 untouched cycle lines.

**Step 7 (calibration model).**
- Let `H = <a, b | (a^m b)^n>`, with `m >= 1` and `n >= 3`, and put `x = a^m b`.  Then `H = <a> * <x | x^n>` and
  `b = a^{-m} x`.
- The element `alpha = sum_{j<n} x^j` with `u = 1`, `w = -a^m` gives `alpha (1 - x) = 1 - x^n = 0`, over every
  field.  Also `u(1) + w(1) = 0`, and `u/w = -t^{-m}` is not constant.
- *Coset graph.*  The active cosets are `T_j = x^j <a>`, for `j` mod `n`.  They are distinct, since
  `x^i ∉ <a>` for `0 < i < n`.
  - `supp Y ∩ T_j = {x^j a^m}`, and `x^j a^m b = x^{j+1}`.  So `Lambda` is the directed `n`-cycle, with in- and
    out-degree 1.
  - *Simple.*  A loop would need `b in <a>`.  Parallel edges would need `x^{-1} a^s x in <a>` for some `s != 0`.
    A 2-cycle would need `x a^s x in <a>` for some `s`, which fails for `s != 0` by reduced length and for `s = 0`
    because `n >= 3`.  In the free product none of these holds.
- *Remaining hypotheses.*
  - On every coset, `P = 1` and `Q = -t^m`, so the rank-one identities `P_T Q_T' = P_T' Q_T` hold.
  - The supports force `f_T in k`, so every coset is locally rigid.
  - A solution exists, so every forced ratio product has the value that the holonomy identity prescribes.
- *Its cycle.*  `c` is minus the relator loop `(a^m b)^n` from `1`: the `b`-edges `[x^j a^m -> x^{j+1}]` and the
  segments `phi = -(1 + ... + t^{m-1})` on each `T_j`.
  - So the splitting is one copy, and all `n` lines are untouched and pure.
  - They all have the port set `{0, m}`, so their difference sets coincide and the rank-one lemma is silent.
- *Conclusion.*  The step "exclude `F_2` harmonic families from support matching, simplicity of `Lambda`, degrees
  and the rank-one lemma" cannot be completed as stated, and neither can the rigid-cycle holonomy step.
  - Every such hypothesis holds in `H`, and `H` has the zero divisor.
  - A proof must use a fact about `K` that fails in `H`: row separation (used in Step 4), or the non-monomial ratio
    (torsion-freeness: `alpha (1 + lambda a^s b) = 0` would make `supp alpha` invariant under the infinite-order
    element `a^s b`).
