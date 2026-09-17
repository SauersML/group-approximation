---
rg: 2
id: fpbs-soft-collapse-on-wreath-and-split-extensions-proof
kind: route
title: Select left cosets of a non-commensurated subgroup iid and connect them through infinitely many disjoint conjugated bypasses
target: fpbs-soft-collapse-on-wreath-and-split-extensions
requires:
  - fpbs-soft-collapse-iff-invariant-sparse-spines
---

Notation as in the target. `Gamma` acts on itself, on `Gamma/K` and on
subgraphs of `G = Cay(Gamma,S)` by left multiplication. "Invariant" means
`Gamma`-invariant in law. Theorem A of
`fpbs-soft-collapse-iff-invariant-sparse-spines` is used verbatim: *`G` carries
a soft collapse family if and only if it has invariant sparse spines* (for
`Gamma` infinite, nonamenable, finitely generated). The target's last clause
follows from Theorem 1 by Theorem A, and Corollary 4 then follows by the
argument of Corollary C there. The work is Theorem 1 and the membership checks.

## 0. Preliminary: (B3) forces infinite index

If `[Gamma:K] < infinity`, the infinite set `Y` meets some left coset `gK` in an
infinite set, which contradicts (B3) with `p = e`. So `Gamma/K` is infinite.

## 1. The coset graph

Fix a finite generating set `T` of `K` and a finite symmetric generating set
`S_0` of `Gamma`. Let `Sigma = S_0 ∪ Sigma_1 ∪ Sigma_1^{-1}`, a finite
symmetric set. The coset graph `A` has vertex set `Gamma/K`. Two distinct
cosets `c, c'` are adjacent if there are `g in c` and `s in Sigma` with
`gs in c'`. The edge set is invariant under left multiplication, and `A` may
have infinite degree.

**Lemma 1.1.** `A` is connected.

*Proof.* If `x = s_1 ... s_n` with `s_i in S_0`, then consecutive cosets in
`K, s_1K, s_1s_2K, ..., xK` are equal or adjacent, witnessed by
`g = s_1 ... s_{j-1}` and `s = s_j`. ∎

**Lemma 1.2 (end edges of a bypass).** If `y in K Sigma_1 K`, then `K` and `yK`
are equal or adjacent. If `x^{-1} y x in K Sigma_1 K`, then `yxK` and `xK` are
equal or adjacent.

*Proof.* Write `y = k sigma k'` with `k, k' in K` and `sigma in Sigma_1`. Then
`yK = k sigma K`, with `k in K` and `k sigma in yK`. For the second statement,
write `x^{-1} y x = k sigma k'`. Then `yxK = x k sigma K`, with `xk in xK` and
`(xk) sigma in yxK`. ∎

## 2. Disjoint conjugated bypasses

Fix `x in Gamma` with `xK ≠ K`. By Lemma 1.1 choose a path
`K = d_0, d_1, ..., d_m = xK` in `A`, and write `d_j = p_j K` with `p_0 = e`
and `p_m = x`. Let

`Y_x = { y in Y : y in K Sigma_1 K and x^{-1} y x in K Sigma_1 K }`.

By (B2) at `e` and at `x`, `Y` minus `Y_x` is finite, so `Y_x` is infinite.
For `y in Y_x`, the **bypass** is the sequence

`K, y d_0, y d_1, ..., y d_m, xK`.

It is a walk in `A` (consecutive terms equal or adjacent). The steps
`y d_j -> y d_{j+1}` are left translates of edges of the path. The two end
steps are `K -> yK = y d_0` and `y d_m = yxK -> xK`, which are covered by
Lemma 1.2. Its **interior** is `I(y) = { y d_0, ..., y d_m }`.

**Lemma 2.1.** For every coset `c`, the set `{ y in Y : c in I(y) }` is finite.

*Proof.* Write `c = gK`. Then `y d_j = c` means `y p_j K = gK`, that is,
`y in g K p_j^{-1} = (g p_j^{-1}) K^{p_j}`. By (B3), each of the `m+1` sets
`Y ∩ (g p_j^{-1}) K^{p_j}` is finite. ∎

**Lemma 2.2.** There are `y_1, y_2, ... in Y_x` whose interiors `I(y_i)` are
pairwise disjoint and disjoint from `{K, xK}`.

*Proof.* Choose the `y_i` inductively. Suppose `y_1, ..., y_n` are chosen, and
put `F = {K, xK} ∪ I(y_1) ∪ ... ∪ I(y_n)`, a finite set. By Lemma 2.1 only
finitely many `y in Y` have `I(y) ∩ F ≠ ∅`. Since `Y_x` is infinite, pick
`y_{n+1} in Y_x` outside that finite set. ∎

## 3. Iid coset selection

Let `omega in {0,1}^{Gamma/K}` have iid Bernoulli(`eps`) coordinates. Say `c`
is selected if `omega(c) = 1`. The law is invariant under the permutation
action of `Gamma` on `Gamma/K`. Let `A_omega` be the subgraph of `A` induced
on the selected cosets.

**Lemma 3.1.** Almost surely `A_omega` is connected and has infinitely many
vertices.

*Proof.* `Gamma/K` is infinite (section 0), so a.s. infinitely many cosets
are selected, by independence and the second Borel--Cantelli lemma.

Fix distinct cosets `c = gK` and `c' = gxK`, so `xK ≠ K`. Let `y_i` be as in
Lemma 2.2 for this `x`. Left translation by `g` is an automorphism of `A`, so
`c, g I(y_i), c'` is again a walk in `A`. The sets `g I(y_i)` are pairwise
disjoint, avoid `c` and `c'`, and have at most `m+1` elements. The events
`E_i = { every coset of g I(y_i) is selected }` are therefore independent,
with `P(E_i) >= eps^{m+1}`. Almost surely some `E_i` occurs, and then, if `c`
and `c'` are selected, they are joined inside `A_omega`.

There are countably many pairs, so a.s. every two selected cosets are joined
inside `A_omega`. ∎

## 4. The spine (proof of Theorem 1)

Let `S` be any finite symmetric generating set of `Gamma` and `G = Cay(Gamma,S)`.
Take `T` symmetric (replace `T` by `T ∪ T^{-1}`). Fix an S-word `w_s` for each
`s in Sigma ∪ T`, and let `R` be the maximal length of these words. For
`g in Gamma` and a word `w`, let `P(g,w)` be the path in `G` that starts at `g`
and reads `w`.

Define `L = L(omega)` as the union of the paths:

* (i) `P(g, w_t)` for every `g` with `gK` selected and every `t in T`. It ends
  at `gt in gK`.
* (ii) `P(g, w_s)` for every `s in Sigma` and every `g` such that `gK` and
  `gsK` are both selected.

**Equivariance.** For `h in Gamma` put `(h omega)(c) = omega(h^{-1}c)`. The
selection rules depend only on which cosets are selected, and
`h P(g,w) = P(hg,w)`. Hence `L(h omega) = h L(omega)`, and since the law of
`omega` is invariant, so is the law of `L`. `L` is a measurable function of
`omega`.

**Connectivity.** Every vertex of a path in (i) or (ii) is joined inside `L` to
its start `g`, a point of a selected coset. Two points `g, gk` of one selected
coset, with `k = t_1 ... t_r` and `t_i in T`, are joined by concatenating
`P(g t_1 ... t_{i-1}, w_{t_i})`, all of type (i). If selected cosets `c`, `c'`
are adjacent in `A`, there are `g in c` and `s in Sigma` with `gs in c'`, and
`P(g, w_s)` is of type (ii) and joins them. By Lemma 3.1 `A_omega` is connected
a.s., so `L` is connected a.s.

**Infinite.** `L` contains every point of each selected coset. Such cosets
exist a.s. and `K` is infinite.

**Density.** If `o in V(L)`, then `o` lies on a path `P(g,w)` of type (i) or
(ii) with `gK` selected and `d_G(o,g) <= R`. Hence

`P(o in V(L)) <= sum_{g in B_R(o)} P(gK selected) = |B_R| eps`.

Given `delta > 0`, take `eps = delta / |B_R|`. `R` does not depend on `eps`.
This gives an invariant, a.s. connected, infinite random subgraph with
`P(o in V(L)) <= delta`. So `G` has invariant sparse spines. When `Gamma` is
nonamenable, Theorem A gives a soft collapse family on `G`. ∎

## 5. Membership checks

**Corollary 2 (split extensions).** Here `Gamma = N ⋊ K`, the group `K` is
infinite and finitely generated, `sigma in N` has finite `N`-conjugacy class
`sigma^N`, and `Y = { k sigma k^{-1} : k in K }` is infinite. Put
`Sigma_1 = sigma^N`.

*(B2).* Let `x = n k_0` with `n in N` and `k_0 in K`, and let
`y = k sigma k^{-1}`. Put `n' = k^{-1} n k in N`. Then
`n^{-1} k sigma k^{-1} n = k (n'^{-1} sigma n') k^{-1}`, so

`x^{-1} y x = (k_0^{-1} k) (n'^{-1} sigma n') (k^{-1} k_0) in K sigma^N K`.

This holds for **every** `y in Y`.

*(B3).* `Y ⊆ N`. If `y, y' in Y ∩ g K^p`, then
`y^{-1} y' in N ∩ p K p^{-1} = p (N ∩ K) p^{-1} = {e}`, using normality of `N`.
So `|Y ∩ g K^p| <= 1`.

For `Z wr F_2 = (⊕_{F_2} Z) ⋊ F_2`, take `sigma` a generator of the lamp at
`e`. `N` is abelian, so `sigma^N = {sigma}`, and the orbit is infinite. The
same works for any abelian `N` with a point of infinite `K`-orbit.

**Corollary 3 (wreath products).** `Gamma = N ⋊ Q` with `N = ⊕_X A`, and
`q a_v q^{-1} = a_{qv}`, where `a_v` is `a in A` placed at coordinate `v`.
`Gamma` is generated by a finite generating set of `Q` together with a finite
generating set of `A` placed at one point of each of the finitely many orbits,
so it is finitely generated. Put `K = Q`, which is infinite and finitely
generated. Fix `a in A` with `a ≠ e` and a point `v_0` of an infinite orbit
`O`. Put `Y = { a_v : v in O }`, which is infinite, and `Sigma_1 = {a_{v_0}}`.

*(B2).* Let `x = eta q` with `eta in N` and `q in Q`. For the cofinitely many
`v in O` outside the finite support of `eta`, `eta` commutes with `a_v`, so
`x^{-1} a_v x = q^{-1} a_v q = a_{q^{-1} v}`. Since `q^{-1} v in O`, choose
`r in Q` with `r v_0 = q^{-1} v`. Then `a_{q^{-1} v} = r a_{v_0} r^{-1} in Q Sigma_1 Q`.

*(B3).* As for Corollary 2: `Y ⊆ N` and `N ∩ Q^p = {e}`.

**Nonamenability.** `Gamma` is amenable iff `A` and `Q` are, because `N`
contains a copy of `A`, `Q` is a quotient, and amenability is closed under
extensions and directed unions. `Z/2 wr F_2`, `Z wr F_2`, `F_2 wr Z` and
`F_2 wr F_2` are nonamenable. So are `A wr_{Q/H} Q` for `Q` nonamenable, where
`H` has infinite index so that `Q/H` is an infinite orbit.

## 6. Corollary 4

This is the argument of Corollary C of
`fpbs-soft-collapse-iff-invariant-sparse-spines`, applied to the families
produced here. A soft argument proving nonuniqueness at some `t > p_c` applies
equally to the family of Theorem A, which satisfies (S1)--(S4). By (S4) that
family has a unique infinite cluster for every `t > p_c`, a contradiction. The
invariant and the failing step are those named in Theorem A. ∎
