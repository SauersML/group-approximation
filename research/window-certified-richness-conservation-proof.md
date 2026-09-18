---
rg: 2
id: window-certified-richness-conservation-proof
kind: route
title: Certification makes h constant on components of each window relation, fibre counting splits them into forced 2-blocks and partial bijections, the derived unique game loses only the forced mass, forced pairings are counted against richness, and Goursat's lemma makes coset windows pure
target: window-certified-richness-is-conserved-modulo-merges
requires: []
artifacts:
  - experiments/rich-2to1-window-components-2026-09-17/check_window_components.py
---

Notation is as in the target claim.

The value of `W` at a left labelling `L` is the best choice of right labels:

```text
val_W(L) = sum_z w_z max_(m in [k]) Pr_(u ~ nu_z)[ h_(uz)(L_u) = m ].
```

## (1) Component lemma

Fix `z` and `u != u'` in `S_z`. By (SLC), every edge `(a, a')` of `R_(uu')`
has `h_(uz)(a) = h_(u'z)(a')`. So every connected component lies inside one
`h_(uz)^(-1)(c) x h_(u'z)^(-1)(c)`, which has 2 + 2 nodes, and `h` is constant
on it.

By (Full), every `a in Sigma_u` extends to some `f in A_z`, and `(a, f_(u'))` is
an edge. So no node is isolated, and the same holds on the `u'` side. A
bipartite graph on 2 + 2 nodes with no isolated node is either connected, giving
one `(2,2)` component, or a perfect matching, giving two `(1,1)` components. If
it is disconnected, some component has at most one node per side and at least
one edge, so it is a single edge, and the complementary pair of nodes is then
matched too.

*Intrinsic description of forced blocks.* If `a != b` share a neighbour `a'`,
their component has two left nodes, so it is `(2,2)`. Conversely, a connected
bipartite graph on `{a,b}` and `{x,y}` contains a path of length 3. That path has
the form `a-x-b-y` or `x-a-y-b`, so some right node is adjacent to both `a` and
`b`. So `F_(uz)` is the union over `u'` of the `u`-sides of the `(2,2)`
components of `R_(uu')`. It depends on `A_z` only.

*Every certified family contains the forced blocks.* Let `g_v : Sigma_v -> [k]`
be any 2-to-1 family satisfying (SLC) over `A_z`. If `(a,a')` and `(b,a')` lie
in `R_(uu')`, then `g_u(a) = g_(u')(a') = g_u(b)`. Since `a != b` and fibres
have size 2, `{a,b}` is a fibre of `g_u`. Blocks coming from different `u'` are
fibres of the single map `h_(uz)`, so they are equal or disjoint, and `F_(uz)` is
a partial pairing contained in `P_(uz)`.

On the `(1,1)` components each left node has exactly one neighbour. This
defines the partial bijection `phi_(uu')` on `X_(uu')`, and `h` is compatible
with it because `h` is constant on components.

*Mixed relations exist.* Take `k = 2`, `Sigma = {0,1,2,3}`, `h(x) = floor(x/2)`
and the single source constraint

```text
R = {(0,0), (0,1), (1,0), (1,1), (2,2), (3,3)}.
```

It satisfies (Full) and (SLC) with `h_u = h_(u') = h`. Fibre 0 is forced and
fibre 1 is bijective. `R` has 6 elements, and 6 does not divide 16, so `R` is
not a coset for any group structure on the alphabets. The artifact's Part A finds
8 mixed relations among 60 feasible random windows, and checks A1 to A3 and A6.

## (2) Value floor and transfer

*`val_W >= val_D`.* For each `z`, a best right label is at least as good as the
random label `m = h_(u_0 z)(L_(u_0))` with `u_0 ~ nu_z`. So

```text
max_m Pr_u[ h_(uz)(L_u) = m ] >= Pr_(u_0, u)[ h_(uz)(L_u) = h_(u_0 z)(L_(u_0)) ]
                              >= Pr_(u_0, u)[ (L_(u_0), L_u) in R_(u_0 u) ].
```

The second inequality holds because an edge of `R` has equal `h`-values, and for
`u_0 = u` both sides equal 1. Summing over `z` gives `val_W(L) >= val_(D_W)(L)`.

*`val_D >= val_U`.* Every edge `(x, phi(x))` lies in `R`.

*`val_U >= val_Ũ - phi_W`.* Suppose `Ũ` accepts but `U` rejects. Then
`L_(u_0)` is outside `X_(u_0 u)`, so `R_(u_0 u)` has a `(2,2)` component, and so
`F_(u_0 z)` is nonempty. That event has probability `phi_W`. The two complements
`Sigma_(u_0) \ X` and `Sigma_u \ X'` have equal size, twice the number of forced
fibres, so a completion to a permutation exists.

*Completeness.* Suppose `L` satisfies `B_z`. Then `L|S_z in A_z`, so every pair
`(L_(u_0), L_u)` lies in `R_(u_0 u)`. If moreover `L_(u_0) in X_(u_0 u)`, its
component is `(1,1)`, so `L_u = phi_(u_0 u)(L_(u_0))`. So `Ũ` can reject only if
`z` is violated, which has mass at most `beta`, or `F_(u_0 z)` is nonempty, which
has mass `phi_W`. So `val_(Ũ_W)(L) >= 1 - beta - phi_W`.

*Transfer.*

* YES instances: `val(Ũ) >= 1 - beta - phi`.
* NO instances: `val(Ũ) = max_L val_Ũ(L) <= max_L val_W(L) + phi <= s + phi`.

Computing `A_z`, its components and the completions takes time polynomial in
`|Sol(B_z)|` and `k`. The artifact's check A4 verifies the chain
`val_W >= val_D >= val_U - phi` exhaustively over all labellings on 25 wrappers.
Check A5 verifies that `phi` is at most the forced edge mass.

## (3) Forced-mass entropy count

By the definitions of `mu` and the edge law,

```text
phi_W = sum_z w_z sum_u nu_z(u) [F_(uz) != empty] = sum_u mu(u) Pr_(z|u)[ F_(uz) != empty ].
```

At a fixed `u`, the events `F_(uz) = t` are disjoint for distinct `t`, and each
implies `t` is contained in `P_(uz)` by (1). So

```text
Pr_(z|u)[ F_(uz) != empty ] <= sum_(t in F_u) Pr[ t in P_(uz) ].
```

A `j`-block partial pairing lies in `(2k-2j-1)!!` of the `(2k-1)!!` pairings.
This gives the full-richness bound. Under (R2), a 1-block `t` has probability
`1/(2k-1)`. A `t` with at least 2 blocks is at most as likely as two of its
blocks together, which has probability `1/((2k-1)(2k-3))`.

For whole pairings, `j = k` and `(-1)!! = 1`. If
`N_k(u) = 2^(o(k log k))`, then `N_k(u)/(2k-1)!! = o(1)`, since
`log (2k-1)!! = k log k + O(k)`. The gate is the contrapositive of the bound.

## (4) Coset sources

*Cosets.*

* Each constraint of `B_z` is a left coset of a subgroup of the product over its
  variables. Its cylinder in the full product `Gamma` of the window's groups is a
  left coset of `Gamma`.
* A nonempty intersection of left cosets `xK` and `x'K'` equals `y(K cap K')` for
  any `y` in it. So `Sol(B_z)` is empty or a left coset.
* Projections are homomorphisms, so `A_z` and `R_(uu')` are left cosets. For a
  feasible window, `R_(uu') = (a_0, a_0') T`.
* (Full) gives `a_0 pi_1(T) = H_u`, so `pi_1(T) = H_u`, and likewise
  `pi_2(T) = H_(u')`.

*Goursat structure.*

* Let `N = {x : (x,1) in T}` and `N' = {y : (1,y) in T}`. These are subgroups.
  For `(y,y') in T`, conjugating `(x,1)` gives `(y x y^(-1), 1)`, so `N` is
  normal in `pi_1(T) = H_u`.
* Write `(a,a') = (a_0 x, a_0' y)`. The edge relation is `(x,y) in T`.
* If `(x,y)` and `(x_2,y)` are in `T`, then `(x^(-1) x_2, 1) in T`, and
  conversely `(x,y)(n,1) in T`. So the left neighbourhood of a right node is
  `a_0 x N`, and symmetrically right neighbourhoods are cosets of `N'`.
* If `(x,y)`, `(x,y_2)` and `(x_2,y)` are in `T`, then
  `(x_2,y_2) = (x_2,y) (x,y)^(-1) (x,y_2)` is in `T`. So each component is the
  complete bipartite graph on `a_0 xN` and `a_0' yN'`.
* Counting, `|T| = |H_u| |N'| = |H_(u')| |N|`, so `|N| = |N'|`. Every component
  has size `(|N|, |N|)`, so the relation is pure.

*Cases.*

* `|N| > 2`. Components have more than 2 labels per side, which contradicts (1).
* `|N| = 1`. `T` is the graph of an isomorphism `theta : H_u -> H_(u')`, so
  `R = { (a, a_0' theta(a_0^(-1) a)) }`.
* `|N| = 2`. `N = {1, b}` is normal, and conjugation fixes `1`, so it fixes `b`.
  So `b` is a central involution. The components' `u`-sides are `{y, yb}`, and
  every fibre is forced, so `P_(uz) = P_b`. By `|N'| = 2` the same holds at `u'`.

*Dichotomy.* Let `R_(uu')` be forced, with `P_(uz) = P_b`, and take any
`u''` in `S_z`.

* If `R_(u u'')` is forced, `P_(u'' z) = P_(b'')` for a central involution `b''`.
* Otherwise `R_(u u'')` is a coset bijection `phi(a) = a_0'' theta(a_0^(-1) a)`,
  and `h_(u'' z) o phi = h_(uz)`. So the fibres at `u''` are
  `phi({y, yb}) = {w, w theta(b)}`, and `theta(b)` is a central involution of
  `H_(u'')`.

If no pair is forced, every `R` is a coset bijection. Each `f in A_z` is then
determined by any one coordinate, and `h` is compatible with all the bijections.
So `z` is the right merge of that clique of coset permutation constraints.

*Mass bound.*

* For a pairing `P` of `H_u` and a central involution `b`, let `n_b(P)` be the
  number of blocks of the form `{y, yb}`. Set `Q(P) = sum_b C(n_b(P), 2)`.
* If `P = P_b`, then `n_b = k`, so `Q >= C(k,2)`.
* The `b`-blocks are the `k` cosets of `{1,b}`. They are pairwise disjoint and
  give `C(k,2)` unordered pairs. Each pair is in `P` with probability
  `1/((2k-1)(2k-3))` under (R2).
* So `E Q = c_u C(k,2)/((2k-1)(2k-3))`, and Markov's inequality gives
  `Pr[P_(uz) is a central translation] <= c_u/((2k-1)(2k-3))`.
* Then

  ```text
  w(T) = sum_z w_z [z in T] = sum_u mu(u) Pr_(z|u)[z in T]
       <= sum_u mu(u) Pr_(z|u)[P_(uz) central translation]
       <= c/((2k-1)(2k-3)).
  ```

* Since `c_u <= 2k-1`, the bound is at most `1/(2k-3)`.
* Under full richness, the `c_u` pairings `P_b` are distinct, since any block
  determines `b`. Their probability is `c_u/(2k-1)!!`.

*Floor.* On type-(D) vertices `D_W` and `U_W` agree, and type-(T) vertices
contribute at least 0. So `val_W(L) >= val_D(L) >= w(D) val_(U^D_W)(L)`. The
violated windows among type (D) have mass at most `beta`, so
`val_(U^D_W)(L) >= 1 - beta/w(D)`.

*Artifact checks.*

* Part B: over `Z_4`, `Z_2^2`, `Z_6`, `S_3`, `D_4`, `Q_8` and `Z_2^3`, every
  projected pair relation is pure. Forced relations have a central involution
  kernel, and at forced vertices every class is a central translation.
* Part C: exhaustively over pairings, `E Q` matches the formula, and the Markov
  bound holds. It is tight on `Z_4` (1/3) and `Z_6` (1/15). `D_4` and `Q_8` give
  `1/105 <= 0.0286`, and `Z_2^3` gives `7/105 <= 0.2`. `S_3` gives 0.

## Where the class dies

Steps (1) and (2) hold for every source. A 2-to-1 map can absorb only
components with at most 2 labels per side. So everything it certifies is either
a bijection, which is merged into `U_W`, or a forced block, which the source
already derives.

The richness hypothesis enters only through (3) and (4). There it bounds the
forced mass by the entropy of the source's forced pairings, and for coset
sources by `c/((2k-1)(2k-3))`.
