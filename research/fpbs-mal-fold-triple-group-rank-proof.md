---
rg: 2
id: fpbs-mal-fold-triple-group-rank-proof
kind: route
title: Cone off the fiber product of the level with core(K), gauge the type-0 cone edges to 1, and read the four Delta-edge relations as one fold triple relation per point
target: fpbs-mal-nonabelian-certificates-are-fold-triple-group-rank
requires:
  - fpbs-mal-modp-promotion-certificates-are-fox-annihilators
artifacts:
  - experiments/fpbs-pushout-level-2026-09-17/tc.py
  - experiments/fpbs-pushout-level-2026-09-17/pushout.py
  - experiments/fpbs-pushout-level-2026-09-17/fib_check.py
  - experiments/fpbs-pushout-level-2026-09-17/fib_check_out.txt
  - experiments/fpbs-pushout-level-2026-09-17/census.py
  - experiments/fpbs-pushout-level-2026-09-17/census_out.txt
---

## 0. Setting and notation

- `L = F(a, b)`, `c = b a b^-2`, `K = <a, c>` (malnormal, free of rank 2).
- A *level* is a finite transitive right `L`-set `V` with base point `v0`,
  `H = Stab_L(v0)`, and `t` the number of `K`-orbits on `V`.
- `M_H` is the normal closure in `H` of all `H cap l K l^-1` (`l` in `L`).
  Equivalently, it is generated as a normal subgroup of `H` by the
  path-conjugates of the `K`-stabilizers `Stab_K(v)`, `v` in `V`.
- For a normal level `V = G = L/N` one has `H = N` and
  `H/M_H = N / <<K cap N>>^L`. This is the non-abelian certificate group
  named by the w13 survivors.
- `core(K)` is the Stallings graph of `K` on vertices `{0, 1, 2}`:
  - `a`-edges `0 -> 0` and `1 -> 2`;
  - `b`-edges `0 -> 1` and `1 -> 2`.

  The loop `0 -b-> 1 -a-> 2 -b^-1-> 1 -b^-1-> 0` reads `c`.
- The *fold triple group* of `V` is

```text
T_V = < y_w  (w in V)  |  y_w = y_{w a b^-1} y_{w a}  (w in V) >.
```

This is a deficiency-zero presentation with `|V|` generators and `|V|` relators.

## 1. Level count lemma (recalled)

**Lemma 1.** Let `Y` be a graph on `V` made of the `a`- and `c`-edges plus `E`
extra edges `v -> v.l_i`, whose loop labels generate the stabilizers. Then
`E >= (t - 1) + d(H/M_H)`.

*Proof.*
1. The loop-label map `pi_1(Y, v0) -> H` is onto.
2. Let `Y_K` be the subgraph of `a`- and `c`-edges. It has `t` components.
3. The loops of the component through `v` have labels in `Stab_K(v)`, after
   conjugating by a path label. So they map into `M_H`.
4. Collapse each component of `Y_K` to a point. The quotient
   `pi_1(Y)/<<pi_1(Y_K components)>>` is the fundamental group of a graph with
   `t` vertices and `E` edges, which is free of rank `E - t + 1`.
5. By steps 1 and 3 this free group surjects onto `H/M_H`. Hence
   `E - t + 1 >= d(H/M_H)`. QED.

This is the same argument as the proof of Theorem 2 in
`research/fpbs-mal-modp-promotion-certificates-are-fox-annihilators-proof.md`,
with `d(H/M_H)` in place of its mod-p homology.

## 2. Theorem A (fold triple group identity)

**Theorem A.** `H/M_H` is isomorphic to `T_V / <<y_{w_1}, ..., y_{w_{t-1}}>>` for
suitable points `w_1, ..., w_{t-1}` of `V`. For a normal level with
`Kbar = G` (`t = 1`) this reads `N/<<K cap N>>^L = T_G`.

*Proof.*

1. *Schreier graph.* `S = Sch(V; a, b)` has edges `a_v : v -> va` and
   `b_v : v -> vb`, and `pi_1(S, v0) = H`.
2. *Fiber product.* `P = S x core(K)` has vertex set `V x {0,1,2}` and four edge
   families:
   - `(v,0) -a-> (va,0)` and `(v,1) -a-> (va,2)`;
   - `(v,0) -b-> (vb,1)` and `(v,1) -b-> (vb,2)`.

   Every vertex of type 1 or 2 is joined to a type-0 vertex: `(w,1)` receives
   `b` from `(wb^-1,0)`, and `(w,2)` receives `a` from `(wa^-1,1)`. The type-0
   vertices of a component form one `K`-orbit. So `P` has exactly `t`
   components (only the components that meet type 0 matter, and that is all of
   them).
3. *Images of the components.* By Stallings, the image of `pi_1` of the
   component through `(v,0)` in `pi_1(S)`, conjugated back to `v0` along a path,
   is `Stab_K(v)` up to that path-conjugation. So the normal closure of all
   component images is `M_H`.
4. *Coning.* Let `Z` be `S` with the mapping cylinder of `P -> S` attached and
   each component of `P` coned to a point `p_C`. By van Kampen,
   `pi_1(Z) = H/M_H`. Take the cellular model:
   - vertices are `V` and the `t` cone points;
   - edges are `a_v`, `b_v`, and `e_{i,v} : p_C -> v` for each vertex `(v,i)` of `P`;
   - there is one triangle per edge of `P`, with boundary
     `e_{i,v} x_v e_{j,vx}^-1` for the edge `(v,i) -x-> (vx,j)`.
5. *Gauge.* The `|V|` edges `e_{0,v}` form a forest with `t` stars, one per
   `K`-orbit. Extend it to a maximal tree by `t - 1` further edges
   `e_{1,w_1}, ..., e_{1,w_{t-1}}` joining the stars. This is possible: the
   edge `e_{1,w}` joins the star of the orbit `wK` to the cone point of the
   component of `(w,1)`, which is the star of the orbit `wb^-1 K`. Since `a`
   preserves orbits and `a, b` act transitively, these edges connect all `t`
   stars. Setting the edges of this maximal tree to 1 presents `pi_1(Z)`.
6. *The four relations.* Write `y_w := e_{1,w}`. With `e_{0,v} = 1`:
   - `e_{0,v} a_v = e_{0,va}` gives `a_v = 1`;
   - `e_{0,v} b_v = e_{1,vb}` gives `b_v = y_{vb}`;
   - `e_{1,v} a_v = e_{2,va}` gives `e_{2,va} = y_v`, that is `e_{2,w} = y_{wa^-1}`;
   - `e_{1,v} b_v = e_{2,vb}` gives `y_v y_{vb} = y_{vba^-1}`.

   The first three eliminate every `a_v`, `b_v` and `e_{2,*}`. Substituting
   `w = vba^-1` (so `v = wab^-1` and `vb = wa`) in the fourth gives
   `y_w = y_{wab^-1} y_{wa}`, one relation per `w` in `V`.
7. What remains is the presentation of `T_V`, together with the `t - 1`
   additional tree relations `y_{w_i} = 1`. QED.

**Corollary A1.** `d(T_V) - (t-1) <= d(H/M_H) <= d(T_V)`. Hence
`(t-1) + d(H/M_H)` lies in `[d(T_V), d(T_V) + t - 1]`.

**Corollary A2.** Every level graph as in Lemma 1 has `E >= d(T_V)`. Along a free
tower, `t_m/|V_m| = 1/|Kbar_m| -> 0` for normal levels. In general
`t_m/|V_m|` is the mean of `1/|vK|` over `v` in `V_m`. Along a tower whose limit
action is essentially free, the `K`-orbit of almost every point in the limit is
infinite, so its image at level `m` has size tending to infinity. By dominated
convergence `t_m/|V_m| -> 0`. So the
non-abelian certificate density is `d(T_{V_m})/|V_m| + o(1)`.

**Inversion form.** Under `y -> y^-1` on points of `L/H`, the triple
`{w, wa, wab^-1}` becomes the fold triple `{y, ay, by}` of
`research/fpbs-mal-profinite-fold-density-is-finite-percolation.md`. So `T_V` is
the group whose relations are exactly the fold triples of that note, with a group
law in place of a 2-of-3 closure.

## 3. The sandwich

Let `s(V)` be the least size of a seed set `S` in `V` whose closure under the rule
"two of `w, wab^-1, wa` present implies the third" is all of `V`.

**Proposition 3.** For every level `V`, every prime `p`, and every level graph `Y`
as in Lemma 1:

```text
k_u(V)  =  dim H_1(T_V; F_p)  <=  d(T_V)  <=  E(Y),        d(T_V)  <=  s(V).
```

*Proof.*
1. *First equality.* Abelianize mod `p`. The relator of `w` becomes
   `e_w - e_{wab^-1} - e_{wa} = e_w u'` with `u' = 1 - ab^-1 - a` acting on the
   right of `F_p[V]`. So `H_1(T_V; F_p) = F_p[V] / F_p[V] u'`. Its dimension is
   the corank of a square matrix, which equals `dim ker(. u')`. Now
   `b^-1 c b = ab^-1` and `b^-1 c b b = a`, so `u' = b^-1 u b` with
   `u = 1 - c - cb`. Right multiplication by `b` is invertible, so the kernels
   of `u'` and `u` have equal dimension `k_u(V)`.
2. *Middle inequality.* `d >= dim H_1(.; F_p)` for every group.
3. *`d(T_V) <= E(Y)`.* This is Corollary A2 (Lemma 1 with Corollary A1).
4. *`d(T_V) <= s(V)`.* In each relation `y_w = y_{wab^-1} y_{wa}`, any two of
   the three generators determine the third. So `{y_s : s in S}` generates every
   `y_w` in the 2-of-3 closure of `S`. QED.

Consequently, the three certificate classes in play are nested at every
finite level:
- the Fox certificate `k_u`;
- the non-abelian certificate `d(T_V)` (equal to the w13 survivor
  `(t-1) + d(N_m/<<K cap N_m>>^L)` up to an additive error in `[0, t-1]`);
- the percolation seed number `s(V)`.

Both the level count `E` and `s(V)` are upper bounds for `d(T_V)`. This note
does not compare `E` with `s(V)`.

## 4. Theorem B (cyclic levels)

Let `G = Z/n` with `a -> alpha` and `b -> beta` (translations), where
`gcd(alpha, beta, n) = 1`. Then `c -> alpha - beta`, and Theorem A gives

```text
T_G = < y_w  (w in Z/n) | y_w = y_{w + alpha - beta} y_{w + alpha} >,
```

which is a cyclically presented group of Fibonacci type.

For `alpha = 2` and `beta = 1`, `Kbar = G` and `t = 1`, so `N/<<K cap N>>^L = T_G`.
Put `x_i = y_{-i-2}`. The relation becomes `x_{i+2} = x_{i+1} x_i`, which is the
opposite of the Fibonacci relation `x_i x_{i+1} = x_{i+2}`. Every group is
isomorphic to its opposite (via inversion), so `T_G` is isomorphic to the
Fibonacci group `F(2, n)`.

The known orders of `F(2, n)` for `n = 2, ..., 8` are
`1, 8 (Q_8), 5, 11, infinite, 29, infinite`. Coset enumeration of
`L/<<K cap N>>^L` over `K` (`fib_check.py`, output in `fib_check_out.txt`) gives
`|N/M| = 1, 8, 5, 11, (overflow), 29, (overflow)`, matching exactly. This is an
independent end-to-end check of Theorem A. It computes `N/<<K cap N>>^L`
directly from the relators of `Kbar`, without using the triple presentation.

In the Fibonacci case `s(Z/n) <= 2`: the seeds `{0, 1}` give `2`, then `3`, and
so on. So `d(T_G) <= 2` and this cyclic family carries no density, as expected
for an amenable quotient.

## 5. Theorem C (which ways of bounding d(T_V) from below die)

Write `Gamma = H/M_H`. A *certificate* is a computable lower bound for
`d(Gamma)` (or for `d(T_V)`) extracted from a finite quotient.

**C1 (p-quotients).** Let `P` be a finite `p`-group. Then `|Hom(T_V, P)|` is at
most `|P|^{k_u(V)}`, and `d(Q) <= k_u(V)` for every `p`-group quotient `Q` of
`T_V`.

*Proof.* Every homomorphism to a `p`-group factors through the pro-`p`
completion. By the Burnside basis theorem, that completion is topologically
generated by `dim H_1(T_V; F_p) = k_u(V)` elements (Proposition 3). QED.

So every `p`-group certificate is dominated by the Fox certificate at the same
level.

**C2 (Schreier certificates).** Let `U <= Gamma` have index `j`, and consider the
certificate `d(Gamma) >= (dim H_1(U; F_p) - 1)/j + 1`. Then there is a level
`V'` covering `V`, with `|V'| = j |V|`, such that

```text
(t - 1) + (dim H_1(U;F_p) - 1)/j + 1   <=   t + k_u(V')/j,
so, after dividing by |V|:   certificate density  <=  t/|V| + k_u(V')/|V'|.
```

*Proof.*
1. `U = H'/M_H` for a unique `H'` with `M_H <= H' <= H` and `[H : H'] = j`. Let
   `V' = H' \ L`, which covers `V = H \ L` with fibres of size `j`.
2. For every `l`, `H' cap l K l^-1 <= H cap l K l^-1 <= M_H`. Since `M_H` is
   normal in `H`, its normal closure in `H'` stays inside `M_H`. So
   `M_{H'} <= M_H`.
3. Hence `U = H'/M_H` is a quotient of `H'/M_{H'}`. By Theorem A,
   `H'/M_{H'}` is a quotient of `T_{V'}`. So
   `dim H_1(U; F_p) <= dim H_1(T_{V'}; F_p) = k_u(V')`. QED.

The same bound holds for rational `H_1`, since
`dim_Q H_1(U; Q) <= dim_{F_p} H_1(U; F_p)`.

**C3 (towers).** Let `V_m` be the levels of a free profinite witness, and let
`V'_m` be any covers of them. For each nontrivial `g` in `L`, the fixed points of
`g` in `V'_m` map into the fixed points of `g` in `V_m`, and the fibres have
constant size. So the fixed-point fraction in `V'_m` is at most that in `V_m`,
which tends to 0. Hence `(V'_m)` is a sofic approximation of `L = F_2`.

Suppose positive-characteristic sofic Lück approximation holds for the single
element `u` in `F_p[F_2]` along sofic approximations. This is the statement
named in item 4 of `fpbs-mal-modp-promotion-certificates-are-fox-annihilators`.
Then `k_u(V'_m)/|V'_m| -> 0` because `u != 0`, and C2 with Corollary A2 shows
that every Schreier certificate density tends to 0, whatever finite-index
subgroups are chosen at each level.

Unconditionally, a Schreier certificate that stays positive along a tower
produces covers `V'_m` with `k_u(V'_m)/|V'_m|` bounded away from 0. Those covers
are sofic, not necessarily nested, so this would be a counterexample to that
Lück statement.

**C4 (what survives, and exactly where the reduction stops).** Twisted
certificates `d(Gamma) >= dim H_1(Gamma; M)/dim M` for an irreducible
`F_p[Q]`-module `M` of a finite quotient `Q = Gamma/U` are not killed.
- For the regular module, Shapiro's lemma gives
  `H_1(Gamma; F_p[Q]) = H_1(U; F_p)`, so this is exactly C2 and is killed.
- When `p` does not divide `|Q|`, `M` occurs in `F_p[Q]` with multiplicity
  `dim M / e_M`, where `e_M = dim End(M)`. This yields only
  `dim H_1(Gamma; M)/dim M <= e_M k_u(V')/(dim M)^2`.
- To compare with the needed `k_u(V')/|Q|` one would need
  `(dim M)^2 >= |Q|/e_M`, so the reduction fails for small-dimensional `M`.
- Counts `|Epi(T_V, S)|` into non-abelian finite simple `S` are not controlled by
  any `F_p`-homology and are also not killed.

These two classes, low-dimensional irreducible twisted ranks and non-abelian
simple colorings of `T_V`, are the surviving ways to prove `d(T_V) >= eps |V|`.

## 6. Census (`census.py`, output `census_out.txt`)

The census covers random 2-generated permutation levels in `S_4`, `S_5`,
`PSL_2(5)` and `PSL_2(7)` (in their natural actions), at normal levels
`G = L/N`. It computes by coset enumeration:
- `|N/M|`, where `M = <<K cap N>>^L`. At normal levels `M = M_N`, and
  `N/M = T_G/<<t-1 tree generators>>`;
- `k_u` over `F_2` and `F_3`.

Checks, row by row:
- `|G| = 3`, `t = 1`, `|N/M| = 8`, with `k_u(F_2) = 2`: this is `Q_8 = F(2,3)`,
  and `d(Q_8) = 2 = k_u`.
- `|G| = 3`, `|N/M| = 7`: this is `Z/7`, with `k_u = 0` at `p = 2, 3`.
  `|G| = 4` gives `Z/5`, and `|G| = 10` gives `Z/3` with `k_u(F_3) = 1`.
- `|G| = 6`, `|N/M| = 56` with `k_u = 0` at `p = 2, 3`: this is consistent with
  `(Z/2)^3 : Z/7`, whose abelianization is `Z/7`.
- `|G| = 12`, `|N/M| = 120` with all `k_u = 0`: this is consistent with a
  perfect group such as `SL_2(5)`.
- The `t > 1` rows satisfy `dim H_1(N/M; F_p) >= k_u - (t - 1)`, as Theorem A
  requires. For example `|G| = 24`, `t = 3`, `|N/M| = 8`, `k_u(F_2) = 4` forces a
  non-cyclic group of order 8.
- Most `t = 1` levels of order `>= 12` overflow (`None`): `T_G` is large or
  infinite there, and `d(T_G)` is undecided.
- The largest Fox densities seen are `k_u(F_2)/|G| = 6/24` in `S_4` and `15/168`
  in `PSL_2(7)`. These are single levels, not nested towers.

## 7. What this does and does not decide

- It decides the exact shape of the w13 survivor "non-abelian certificates
  `d(N_m/<<K cap N_m>>^L)`". Up to `o(|V_m|)`, it is the generation rank of one
  explicit deficiency-zero group per level, with one fold triple relation per
  point.
- It places that rank as `k_u <= d(T_V) <= min(E, s(V))`.
- It removes `p`-quotient certificates unconditionally (they are at most `k_u`).
- It removes Schreier (finite-index `H_1`) certificates conditionally on the
  positive-characteristic sofic Lück statement for `u`, and unconditionally
  turns any positive Schreier certificate into a counterexample to that
  statement.
- It does not decide D0 or `fpbs-mal-bernoulli-single-stage-floor`. Whether
  `inf_m d(T_{V_m})/|V_m| > 0` along some free tower is open. The surviving
  proof classes are named in C4.
