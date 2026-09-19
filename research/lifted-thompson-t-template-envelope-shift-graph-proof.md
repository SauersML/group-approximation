---
rg: 2
id: lifted-thompson-t-template-envelope-shift-graph-proof
kind: route
title: Read Cay(Gamma, sD) as the line digraph of a conjugation orbital, then realise the triple shift graph with affinely transported copies of x_0 in F
target: lifted-thompson-t-template-envelope-contains-shift-graphs
requires: []
---

Complete direct proof.  Item 1 is elementary group theory plus two
classical line-digraph colouring facts, which are reproved here.  Item 2
uses only standard facts about Thompson's group `F` (Cannon–Floyd–Parry,
Lemma 4.2 and the PL description).  Nothing needs Lean.

## Item 1

**1a (cosets).**  Fix `f in F`, `f_1 in F_1` with `[f,h] = 1`, and let

```text
S_{f,f_1} = {k : kck^(-1) = f,  k^(-1)hk = f_1}.
```

Suppose it is nonempty and contains `s`.  If `k = st`, then the first
condition gives `t in C(c)`.  The second gives
`t^(-1)(s^(-1)hs)t = s^(-1)hs`, so `t in C(f_1)`, because
`s^(-1)hs = f_1`.  So `S_{f,f_1} = s D` with `D = C(c) ∩ C(f_1)`, and
`S(F,F_1)` is the union over the at most `|F||F_1|` such pairs.  Since
`[scs^(-1), h] = [f,h] = 1`, conjugating by `s^(-1)` gives `[c, f_1] = 1`.
Finally `1 ∉ S`, because `[c,h] != 1`.

**1b (line digraph).**  Put `tau(g) = gD` and `eta(g) = gsD`.  For
`w in Gamma` we have `w in gsD` if and only if `wD = gsD`.  So `g -> w` is
an arc of `Cay(Gamma, sD)` if and only if `tau(w) = eta(g)`.  This is the
definition of the line digraph of the multidigraph `Z` whose arcs are the
`g in Gamma`, running from `tau(g)` to `eta(g)`.

A loop `tau(g) = eta(g)` would force `s in D ⊂ C(c)`, hence `f = c`, and
then `[c,h] = [f,h] = 1`, which is excluded.

`D` is the stabilizer of `P = (c, f_1)` under simultaneous conjugation.
So `gD -> gPg^(-1)` identifies `Gamma/D` with the orbit of `P`, and it
sends the arc `g` to the pair `g·(P, sP)`.  The underlying simple digraph
is therefore the orbital digraph of `(P, sP)`.

**1c (colouring line digraphs).**  These facts are due to Harner–Entringer
and Poljak–Rödl.  The proofs hold verbatim for infinite multidigraphs
without loops.

- *Lower bound.*  Let `phi` properly colour `L(Z)` with `k` colours.
  Colour a vertex `p` of `Z` by `Phi(p) = {phi(a) : a leaves p}`.  Let
  `a : p -> q` be an arc.  Then `phi(a) in Phi(p)`.  Every arc `b` leaving
  `q` satisfies `a -> b` in `L(Z)`, so `phi(b) != phi(a)`, and hence
  `phi(a) ∉ Phi(q)`.  Thus `Phi` is a proper colouring with `2^k`
  colours.
- *Upper bound.*  Let `psi` colour `Z` with `m <= binom(k, floor(k/2))`
  colours, and pick distinct middle-layer sets `A_1..A_m ⊂ [k]`.  These
  form an antichain.  Colour an arc `a : p -> q` by any element of
  `A_psi(p) \ A_psi(q)`, which is nonempty because `psi(p) != psi(q)`.
  Consider `a -> b` with `b : q -> r`.  Then `phi(a) ∉ A_psi(q)` while
  `phi(b) in A_psi(q)`.
- *Cliques.*  Suppose `a -> b`, `b -> e` and `a -> e`.  Then
  `tau(b) = eta(a) = tau(e) = eta(b)`, which is a loop.  So there is no
  transitive triangle.  Every tournament on 4 vertices contains one, so
  every undirected 4-clique would too, and `omega(L(Z)) <= 3`.
- *Union.*  `Y` is the union of the `Cay(Gamma, s_i D_i)` on one vertex
  set.  The product colouring gives `chi(Y) <= prod_i chi(L(Z_i))`.
- *Templates.*  `v -> g_v` (the element of `u_v`) sends each arc of `G` to
  an arc of `Y`, by (N), and `1 ∉ S` rules out loops.  So it is a digraph
  homomorphism and `chi(G) <= chi(Y)`.

**1d (commensurated case).**  The out-neighbours of `gD` in the simple
digraph `Z` are `g d s D` for `d in D`.  There are `[D : D ∩ sDs^(-1)]` of
them, since `D` acts on `DsD/D` with that stabilizer.  If this is at most
`m`, then every finite subdigraph on `n` vertices has at most `mn` arcs.
So the underlying graph of every finite subgraph has a vertex of degree at
most `2m`, which makes it `2m`-degenerate and `(2m+1)`-colourable.  By
de Bruijn–Erdős, `chi(Z) <= 2m+1`.  The in-degree version is the same
argument for the reversed digraph.  Then 1c bounds `chi(L(Z_i))`, and 1c
(templates) bounds `chi(G)`.

## Item 2

**Facts about `F`.**  Elements of `F` are the PL homeomorphisms of
`[0,1]` with finitely many dyadic breakpoints and slopes in `2^Z`.

- (F1) For dyadic `p < q` and `p' < q'` there is such a PL map from
  `[p,q]` onto `[p',q']` (CFP, Lemma 4.2).  The increasing affine map
  between two standard dyadic intervals has slope in `2^Z` and a dyadic
  translation.  Take ordered disjoint standard dyadic intervals
  `J_1 < ... < J_n` and `J'_1 < ... < J'_n` in `(0,1)`, with nondegenerate
  gaps on both sides.  Gluing the affine maps `J_r -> J'_r` with (F1) maps
  on the gaps gives `t in F`, affine from `J_r` onto `J'_r`.
- (F2) Let `phi_J` be the affine map from `[0,1]` onto `J`.  Then
  `c_J = phi_J x_0 phi_J^(-1)` on `J` and `c_J = id` off `J` lies in `F`.
  If `t in F` is affine from `J` onto `J'`, then `t c_J t^(-1) = c_{J'}`:
  both sides are the identity off `J'`, and `t phi_J = phi_{J'}`.
- (F3) `x_0(y) < y` on `(0,1)`, so `c_J` has no fixed point in `int J`.
- (F4) `F = Stab_T(0)`.  Lifting each element to the lift fixing `0` gives
  an injective homomorphism `F -> T̄`.  All identities below are identities
  in `F`, hence in `T̄`.

**Data.**  Put `phi_j(y) = 2^(-2j) y`.  This is the increasing affine map
from `sK = [1/4,1/2]` onto `E_j = [2^(-2j-2), 2^(-2j-1)]`, and
`alpha_j = phi_j(I) = [5·2^(-2j-4), 6·2^(-2j-4)] ⊂ int E_j`.

- `s` exists by (F1).  It sends the ordered pair `I < K` to `sI < sK`.
- `t_{ijl}` for `i < j < l` exists by (F1).  It sends
  `sI < sK < K` to `alpha_l < E_j < E_i`.  All gaps are nondegenerate:
  - `6·2^(-2l-4) < 2^(-2j-2)`, since `l >= j+1`;
  - `2^(-2j-1) < 2^(-2i-2)`, since `i <= j-1`;
  - the end gaps are nondegenerate as well.
- Its restriction to `sK` is the unique affine map onto `E_j`, which is
  `phi_j`.  So `t_{ijl}(I) = alpha_j`.

**Checks.**  Let `a = (i,j,l)` and `b = (j,l,m)`, and write `t_a`, `t_b`.

1. *Mark.*  `h = c_{sK}` has no fixed point in `int sK`, which contains
   `5/16`, by (F3).  So `h(int I) != int I`, hence `h c h^(-1) != c`, and
   `x != 1`.  CCC1 is the free identity
   `[u c u^(-1), u h u^(-1)] = u [c,h] u^(-1)`.
2. *Exact commutation.*  By (F2):
   - `C_b = t_b c_I t_b^(-1) = c_{alpha_l}`, because `t_b` is affine on
     `sK ⊃ I` with `t_b(I) = alpha_l`;
   - `H_a = t_a c_{sK} t_a^(-1) = c_{E_j}`.

   Now `alpha_l ⊂ E_l`, and `E_l` lies left of and is disjoint from `E_j`,
   so the two elements commute.
3. *Condition (N).*  Put `k = t_a^(-1) t_b`.
   - `k c k^(-1) = t_a^(-1) c_{alpha_l} t_a = c_{sI}`, since `t_a` is
     affine from `sI` onto `alpha_l`.
   - `k^(-1) h k = t_b^(-1) c_{E_j} t_b = c_K`, since `t_b` is affine from
     `K` onto `E_j`.

   Moreover `k|_I = s|_I` (onto `sI`) and `k|_K = s|_K` (onto `sK`), so
   `d = s^(-1) k` fixes `I ∪ K` pointwise and lies in
   `C(c) ∩ C(c_K) = D`.
4. *Infinitely many `k`.*  Suppose the `k` took finitely many values.
   Fix `b = (j,l,m)` and let `i < j` vary.  Then
   `t_{ijl} = t_b k^(-1)` takes finitely many values.  But
   `t_{ijl}(K) = E_i` are pairwise distinct, a contradiction.
5. *Chromatic number.*  Let `TT` be the transitive tournament on `N`.
   Then `Sh_2(N) = L(TT)`, with arcs `(i,j) -> (j,l)`, and
   `Sh_3(N) = L(Sh_2(N))`.  `TT` has no finite proper colouring.  Applying
   the lower bound of 1c twice, neither does `Sh_3(N)`.
6. *Triangle-free.*  A transitive triangle is excluded by 1c.  A directed
   3-cycle would need the index triples to increase cyclically, which is
   impossible.  So `omega = 2`.

So `Sh_3(N)` with the words `u_{ijl}` is a conjugate template satisfying:

- CCC1 with area 0;
- exact commutation on every edge;
- (N) with `F = {c_{sI}}` and `F_1 = {c_K}`.

Its image lies in the single coset `sD`, which gives the explicit
infinite-chromatic line digraph inside the element envelope `Y`.  Whether
(CCC2) holds is a question about the words alone: the area of
`[kck^(-1),h]` for the free words `k = u_a^(-1) u_b`.  This proof does not
decide it.
