---
rg: 2
id: fpbs-commensurated-subgroup-sparse-spines-proof
kind: route
title: Select iid Bernoulli cosets of the commensurated subgroup as sheets, join each sheet by generator words or a summable hierarchical tree, and connect sheets by rare walks whose trajectories are constant on a finite-index subgroup
target: fpbs-commensurated-subgroup-sparse-spines
requires:
  - fpbs-soft-collapse-iff-invariant-sparse-spines
---

## 0. Conventions

- `G = Cay(Gamma,S)` has edges `{x, xs}`; `Gamma` acts on the left.
- For a word `w = s_1...s_l` in `S`, `w_i = s_1...s_i` and `P(x,w)` is the
  path `x, x w_1, ..., x w_l`. Left multiplication maps `P(x,w)` to `P(gx,w)`.
- **MTP.** If `f(x,y,omega) >= 0` is diagonally invariant and `omega` has
  invariant law, then `E sum_y f(o,y) = E sum_x f(x,o)`. (Cayley graphs are
  unimodular; `E f(o,y) = E f(y^{-1},o)` by invariance, then sum over `y`.)
- `H` is infinite, of infinite index and commensurated. Left cosets `gH`
  form the countable set `Gamma/H`, permuted by the left action.

**Lemma 0 (trajectory stabilizer).** Let `w` be a word of length `d` and
`H'_w = H ∩ ∩_{i=1}^{d} w_i H w_i^{-1}`. Then `H'_w` has finite index in `H`,
hence is infinite, and for every `x_0 in Gamma`, `h in H'_w` and `i <= d`,
`x_0 h w_i H = x_0 w_i H`.

*Proof.* Each `H ∩ w_i H w_i^{-1}` has finite index in `H` by commensuration,
and a finite intersection of finite-index subgroups has finite index. If
`h in w_i H w_i^{-1}` then `h w_i in w_i H`, so `x_0 h w_i H = x_0 w_i H`. ∎

## 1. Randomness

All independent:

- `a = (a_c)_{c in Gamma/H}`, iid Bernoulli(`eps`); `A = {c : a_c = 1}`;
- `lambda = (lambda_x)_{x in Gamma}`, iid uniform on `[0,1]`;
- for each `x`, an iid sequence `(s^x_n)_{n>=1}` uniform on `S`;
- `u = (u_{x,t})_{x in Gamma, t in T}`, iid uniform on `[0,1]`, where
  `T = union_k T_k` in case (T2) (unused in case (T1)).

`Gamma` acts on each field by permuting its countable index set on the left
(`(g a)_c = a_{g^{-1} c}`, `(g u)_{x,t} = u_{g^{-1}x, t}`, and so on). Each
field is iid, so the joint law is invariant. Every object below is a Borel
function of the fields that commutes with the action.

## 2. Sheets

For a coset `c = yH` we define a subgraph `Sh_c` that contains `c`, is
connected, and satisfies `g Sh_c = Sh_{gc}` (computed from the translated
fields).

**Case (T1).** Let `h_1..h_m` generate `H`, with `S`-words `v_1..v_m`. Put
`Sh_c = union_{x in c, j} P(x, v_j)`. The path `P(x, v_j)` joins `x` to
`x h_j`, so all of `c = yH` lies in one component, and every vertex of `Sh_c`
lies on a path starting in `c`. Covariance is immediate.

**Case (T2).** For `x in Gamma` and `k >= 1`, the *level-`k` block* of `x` is
`x H_k`; it is the disjoint union of the `[H_k : H_{k-1}]` *children*
`x h H_{k-1}`, `h in H_k`. Blocks and children are defined by right
multiplication, so left multiplication maps blocks to blocks and children to
children.

- *Child graph.* On the children of a block `B`, join child `C` to child `C'`
  by a *candidate edge* `(z,t)` whenever `z in C`, `t in T_k` and
  `z t in C'`, `C' ≠ C`. This graph is connected: `H_k = <H_{k-1}, T_k>`, so
  every `h in H_k` is a product of elements of `H_{k-1}` and of `T_k^{±1}`, and
  multiplying on the right by `H_{k-1}` keeps the child while multiplying by
  `t^{±1}` moves along a candidate edge (for `t^{-1}`, the edge `(z t^{-1}, t)`
  read backwards).
- *Tree.* Give the candidate edge `(z,t)` the weight `u_{z,t}`. The finitely
  many weights in `B` are a.s. distinct; let `Tr_B` be the minimum spanning
  tree of the child graph. It has `[H_k:H_{k-1}] - 1` edges, and is covariant
  because the weights are.
- *Sheet.* `Sh_c = c ∪ union_{k>=1} union_{B subset c level k}
  union_{(z,t) in Tr_B} P(z, w_t)`, where `w_t` is a geodesic `S`-word for `t`.

*Connected.* By induction on `k`, every level-`k` block `B subset c` lies in
one component: for `k = 0` a block is a single point, and a level-`k` block is
the union of its children, each connected by induction, joined along the tree
`Tr_B` by paths `P(z,w_t)` from `z` to `z t`. Any two points `x, x h` of `c`
lie in a common block, since `h in H_k` for some `k`. ∎

## 3. Connectors

For `x` with `xH in A`, let `X^x_n = x s^x_1 ... s^x_n` and
`T_x = inf{n >= 1 : X^x_n H in A \ {xH}}` (possibly `infinity`). The connector
`P_x = (X^x_0, ..., X^x_{T_x})` is *added* exactly when `xH in A`,
`T_x < infinity` and `lambda_x < eta/(T_x+1)`. Let `C` be the union of added
connectors and

```text
L = union_{c in A} Sh_c  ∪  C.
```

Covariance: the walk from `gx` in the translated configuration is `g X^x`, and
`g X^x_n H in gA` iff `X^x_n H in A`. So `L(g.config) = g L(config)` and `L`
has invariant law.

## 4. Density, infinitude, connectivity

**Density.** Send mass from `x` to every vertex of the paths that `x` is
responsible for:

- `f_1(x,y) = 1{xH in A} 1{y = x}`;
- `f_2(x,y) = 1{xH in A} * #{paths of Sh_{xH} started at x through y}`, where
  in case (T1) `x` starts `P(x,v_j)`, and in case (T2) `x` starts `P(x,w_t)`
  for each tree edge `(x,t)`;
- `f_3(x,y) = 1{P_x added} 1{y in V(P_x)}`.

Each is diagonally invariant, and every vertex of `L` receives mass `>= 1`
from `f_1 + f_2 + f_3`. The mass sent by `o`:

- `E sum_y f_1 = P(oH in A) = eps`.
- Case (T1): `E sum_y f_2 <= eps sum_j (|v_j| + 1) = K eps`.
- Case (T2): at level `k`, `o` starts a tree path only if `(o,t)` is a tree
  edge of its level-`k` block `B`. The block has `|H_k|` points and its tree
  has `[H_k:H_{k-1}] - 1 < |H_k|/|H_{k-1}|` edges, each path with at most
  `1 + max_{T_k}|t|_S` vertices. Send instead, from each vertex `x` of `B`, the
  mass `|B|^{-1}` times the total vertex count of the level-`k` tree paths of
  `B`. This is diagonally invariant (the block and tree are covariant), every
  vertex on a level-`k` tree path still receives mass `>= 1` summed over the
  block, and `o` sends at most `eps (1 + max_{T_k}|t|_S)/|H_{k-1}|`. Summing over
  `k` gives `E sum_y f_2 <= K eps`.
- `E sum_y f_3 <= E[1{oH in A} (T_o+1) min(1, eta/(T_o+1)) 1{T_o<infinity}]
  <= eta eps`, since `lambda_o` is independent of `(a, s)`.

By the MTP, `P(o in V(L)) <= (1 + K + eta) eps` with `K` the constant of the
relevant case (`K = sum_j (|v_j|+1)` in (T1)). This tends to `0` with `eps`.

**Infinite.** `Gamma/H` is infinite, so `A ≠ ∅` a.s., and each selected
sheet contains the infinite set `c`.

**Connected.** Sheets are connected and every added connector joins a point of
`Sh_{xH}` to a point of `X^x_{T_x}H subset Sh_{X^x_{T_x}H}`. There are countably
many pairs of cosets, so it suffices to show: for fixed `q ≠ q'` in
`Gamma/H`, a.s. on `{q,q' in A}` the sheets `Sh_q`, `Sh_{q'}` are joined in
`L`. By independence and Fubini, fix `a` with `q, q' in A`.

We prove by induction on `d` the statement **(J_d)**: if `x_0 in q in A`, `w`
is a word of length `d`, and `x_0 w in q' in A`, `q' ≠ q`, then `Sh_q` and
`Sh_{q'}` are a.s. joined. Since `G` is connected, some such word exists for
every pair, which gives the claim.

- Let `C_i = x_0 w_i H`, and let `i_1 in [1,d]` be the least index with
  `C_{i_1} in A \ {q}`; it exists because `C_d = q'`.
- For `h in H'_w` (Lemma 0) put `x = x_0 h in q`, and let `E_x` be the event
  that `s^x_1 ... s^x_{i_1}` equals the first `i_1` letters of `w` and
  `lambda_x < eta/(i_1+1)`. On `E_x`, Lemma 0 gives `X^x_i H = C_i` for
  `i <= i_1`, so `T_x = i_1`, the connector `P_x` is added, and it joins
  `Sh_q` to `Sh_{C_{i_1}}`.
- `P(E_x) = |S|^{-i_1} min(1, eta/(i_1+1)) > 0` does not depend on `x`, the
  events `E_x` for distinct `x` depend on disjoint coordinates and are
  independent, and `x_0 H'_w` is infinite. By Borel--Cantelli II some `E_x`
  occurs a.s.
- If `C_{i_1} = q'` we are done. Otherwise apply (J_{d - i_1}) to the point
  `x_0 w_{i_1} in C_{i_1} in A` and the remaining letters of `w`, which end at
  `x_0 w in q'`, with `q' ≠ C_{i_1}`.

Chaining the two joins proves (J_d). (J_0) is vacuous, as `q ≠ q'` is
impossible with `d = 0`. ∎

This proves the Theorem.

## 5. Corollary and calibration

**Corollary.** For nonamenable `Gamma`, Theorem A of
`fpbs-soft-collapse-iff-invariant-sparse-spines` turns the spines into a soft
collapse family on `Cay(Gamma,S)`.

**Members.**

- `BS(m,n)`, `|m|,|n| >= 2`: it contains `F_2`, so it is nonamenable;
  `<a>` has infinite index (the map `t -> 1`, `a -> 0` onto `Z`); and
  `t a^m t^{-1} = a^n` and `t^{-1} a^n t = a^m` give
  `<a> ∩ t^{±1}<a>t^{∓1}` of finite index in `<a>`. The commensurator of a
  subgroup is a subgroup, so `<a>` is commensurated. Case (T1).
- `A wr Q`, `A` finite nontrivial, `Q` infinite, finitely generated and
  nonamenable: `H = ⊕_Q A` is normal, infinite, of infinite index. Take
  `H_0 = {e}`, `H_k = ⊕_{B_Q(k-1)} A` for `k >= 1`, and
  `T_k = {a delta_v : a in A, v in B_Q(k-1) \ B_Q(k-2)}` (with `B_Q(-1) = ∅`).
  With `S_0 = S_Q ∪ {a delta_e : a in A}`, `|a delta_v|_{S_0} <= 2|v|_{S_Q} + 1`,
  and `|g|_S <= M |g|_{S_0}` with `M = max_{s in S_0}|s|_S`. Since `Q` is
  infinite, `|B_Q(k-2)| >= k-1`, so `|H_{k-1}| >= 2^{k-1}` for `k >= 2`, and
  `K <= (1 + M) + sum_{k>=2} (1 + M(2k-1)) 2^{-(k-1)} < infinity`. Case (T2).
  The group is nonamenable because it contains the nonamenable subgroup `Q`.
- Graphs of finitely generated groups with finite-index edge inclusions: a
  vertex stabilizer `Gamma_v` of the Bass--Serre tree is commensurated, because
  for any `g` the stabilizers along the geodesic from `v` to `gv` are pairwise
  commensurable (consecutive ones share an edge group of finite index in
  both). Case (T1) under the stated hypotheses.

**Spines force cost one (calibration).** Let `L` be an invariant spine of
density `eps`, and `beta` an independent iid uniform `[0,1]` field on `Gamma`. The
action on `(L, beta)` is free. Define a graphing: the edges of `L`, and for
each vertex `x notin V(L)` one edge to the neighbour `xs` with
`dist(xs, V(L)) = dist(x, V(L)) - 1` minimizing `beta` (ties impossible a.s.).
`V(L) ≠ ∅` a.s. by Lemma 0 of `fpbs-soft-collapse-iff-invariant-sparse-spines-proof`,
so each vertex reaches `L` along decreasing distance and `L` is connected: the
graphing generates the orbit relation. Its cost is at most
`eps |S|/2 + 1`. Hence `C(Gamma) = 1` and, by Gaboriau,
`beta_1^{(2)}(Gamma) = 0`. For `F_2` (cost `2`) no subgroup as in the Theorem
exists, and nothing contradicts Lyons, whose theorem concerns groups without
fixed price one; cost one of one free action does not imply fixed price one.
