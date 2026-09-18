---
rg: 2
id: magnus-windows-are-linton-one-relator-towers-proof
kind: route
title: Check Linton's Definition 4.1 on the explicit height windows, read the length-N termination clause of p. 15, then apply Theorem 7.1
target: magnus-windows-are-linton-one-relator-towers
requires:
  - linton-z-stable-one-relator-hierarchy-theorem
artifacts:
  - research/artifacts/one-relator-linton-graph-certificates-scripts/lintongraph.py
---

Page numbers refer to M. Linton, *One-relator hierarchies*, arXiv:2202.11324v3.

## Linton's definitions used

- **One-relator complex.** A pair `(Gamma, lambda)`: a finite graph `Gamma` and one 2-cell
  attached along a closed path `lambda`.
- **Definition 4.1 (p. 4).** `p : Y -> X` is a Z-cover and `t` generates the deck group. A
  *Z-domain* is a subcomplex `D` of `Y` with:
  - (1) `Z · D = Y`;
  - (2) `D cap t^i D ⊂ D cap tD cap ... cap t^i D` for all `i > 0`;
  - (3) `D cap tD` is connected and non-empty.
- **Towers (p. 15).** A sequence of immersions `X_N -> ... -> X_0 = X` is a *one-relator tower*
  when each `X_i` is a one-relator Z-domain of a Z-cover of `X_(i-1)`.
  - Such a tower is a *hierarchy of length N* when "`pi_1(X_N)` splits as a free product of
    cyclic groups".
  - The splitting `pi_1(X_i) = pi_1(X_(i+1)) *_psi_i` comes from Proposition 4.3 and
    Theorem 2.6.
  - Its Magnus subgraphs are `A = t^-1 X_(i+1) cap X_(i+1)` and `B = X_(i+1) cap t X_(i+1)`
    (p. 15), with `t a t^-1 = psi(a)` (p. 23).
- **Z-stable (Definition 1.1, p. 3; p. 31).** A hierarchy is Z-stable when `sZ(psi_i) < infinity`
  for all `i < N`.

## Step 0: normal form of the complexes

We say `X = (Gamma, lambda)` is in **tree form** when:
- `Gamma` has a chosen spanning tree `T`;
- each non-tree edge `e` gives the free generator `g_e` (path in `T`, then `e`, then back);
- `lambda` is cyclically reduced as a word `W` in the `g_e`.

The presentation complex `X_0` of `<a, t | w>` is in tree form, with one vertex, `T` a point,
and non-tree edges `a` and `t`.

## Step 1: one window step

Let `X = (Gamma, lambda)` be in tree form with word `W`, and let `s` be a non-tree edge whose
letter has exponent sum 0 in `W`. The top level uses `s = t`, and level `i` uses the chosen
letter.

**The cover.** Put weight 1 on `s` and weight 0 on every other edge. This defines
`f : pi_1(X) -> Z` with `g_s -> 1`, well defined because `W` has `s`-exponent 0. Let
`p : Y -> X` be the induced Z-cover.
- Its vertices are `(v, h)`, and its edges are `(e, h)`, running from `(o(e), h)` to
  `(t(e), h + wt(e))`.
- `T` lifts to disjoint copies `T × {h}`.
- The 2-cells are the deck translates of one lift `lambda~`.

Along `lambda~`, the height after a prefix is the `s`-exponent of that prefix, because tree
edges have weight 0. For each non-tree edge `u != s` let `[m_u, M_u]` be the heights at which
`lambda~` crosses a copy of `u`. For a generator absent from `W`, fix any single height in
`[m, M]`, as in Magnus–Moldavanskii. Let `[m, M]` be the range of vertex heights on `lambda~`.

`W` is cyclically reduced and contains a letter other than `s^(+-1)`, since its `s`-exponent is
0 and it is not trivial. Suppose `lambda~` reaches height `M` by an `s`-edge. The next letter is
not `s^-1` (reducedness) and not `s` (maximality), so it is some `u` at height `M`. Hence
`M = max M_u`, and likewise `m = min m_u`. Also `M > m`, because `s` occurs.

**The window.** `D` is the subcomplex made of:
- all vertices `(v, h)` and all tree edges `(e, h)`, for `m <= h <= M`;
- the `s`-edges `(s, h)` for `m <= h <= M-1`;
- the edges `(u, h)` for `u != s` and `m_u <= h <= M_u`;
- the 2-cell `lambda~`, whose boundary lies in the listed edges by definition of the ranges.

**Definition 4.1 holds.**
- **(1)** Each vertex, tree edge, `s`-edge and `u`-edge of `Y` has a height, and some translate
  `s^j D` contains that height. Each range is non-empty. Every 2-cell is a translate of
  `lambda~`.
- **(2)** For `j > 0`, `D cap s^j D` consists of:
  - vertices and tree edges at heights `[m+j, M]`;
  - `s`-edges at `[m+j, M-1]`;
  - `u`-edges at `[m_u+j, M_u]`;
  - no 2-cell, because the deck group acts freely on cells.

  `D cap sD cap ... cap s^j D` is the intersection of the same interval families
  `[m+k, M+k]`, `0 <= k <= j`, so it is the same set. Hence (2) holds, with equality.
- **(3)** `D cap sD` contains the vertices at heights `[m+1, M]`, which is non-empty since
  `M > m`. At each height, `T × {h}` connects all vertices, and the `s`-edges `(s, h)`,
  `m+1 <= h <= M-1`, join consecutive heights. So `D cap sD` is connected.

`D` has exactly one 2-cell, so it is a one-relator Z-domain, and `X' := D -> Y -> X` is a tower
map.

**`X'` is in tree form with the Magnus–Moldavanskii word.** Take
`T' = (T × [m, M]) ∪ {(s, h) : m <= h <= M-1}`.
- It is connected.
- It has `|V|(M-m+1) - 1` edges on `|V|(M-m+1)` vertices, so it is a spanning tree.
- The non-tree edges of `D` are the `(u, h)` with `u != s` and `h in [m_u, M_u]`. The
  generator `(u, h)` maps to `s^h u s^-h` in `pi_1(X)`.
- `lambda~` reads `W` with each `u` at height `h` replaced by `u_h`. That is the
  Magnus–Moldavanskii rewriting `W'`.
- `W'` is cyclically reduced. Two adjacent letters `u_h`, `u'_(h')` of `W'` are separated in
  `W` by a block `s^k`. If `k = 0` they are adjacent in `W` and do not cancel. If `k != 0` then
  `h != h'`.

**The splitting is the MM splitting.**
- `A = s^-1 D cap D` has non-tree edges `(u, h)` with `h < M_u`.
- `B = D cap sD` has non-tree edges `(u, h)` with `h > m_u`.
- Translating by `s` sends `(u, h)` to `(u, h+1)`.

So `pi_1(A) = F(u_h : h < M_u)`, `pi_1(B) = F(u_h : h > m_u)`, and `psi(u_h) = u_(h+1)`. These
are the Magnus–Moldavanskii edge groups and gluing (`t a t^-1 = psi(a)` with
`u_(h+1) = s u_h s^-1`). The subgraphs are `pi_1`-injective by Theorem 2.6, the Freiheitssatz
for one-relator complexes. So Proposition 4.3 gives `pi_1(X) = pi_1(X') *_psi`, which is the
one-relator splitting of Theorem 4.13 and p. 15.

At the top level (`X = X_0`, `s = t`), `X'` has vertices `0..n`, the `t`-edges as tree, loops
`a_0..a_n`, and word `W_0`. So `pi_1(X_1) = B_0`, with `A = F(a_0..a_(n-1))`,
`B = F(a_1..a_n)` and `psi(a_i) = a_(i+1)`.

## Step 2: induction and termination

`X'` is again in tree form, so Step 1 applies to it with any letter of exponent sum 0 in
`W'`. By induction the `N` rewritings give a one-relator tower
`X_N -> ... -> X_1 -> X_0`, whose `i`-th splitting is the `i`-th Magnus–Moldavanskii splitting.

If `R_N` is primitive in the free group on the non-tree edges of `X_N`, then
`pi_1(X_N) = F / <<R_N>>` is free, because a primitive element extends to a basis. A free group
is a free product of infinite cyclic groups. So the tower is a **hierarchy of length N** in the
sense of p. 15. Nothing in that definition requires the tower to be maximal, or the last group
to be finite cyclic. Theorem 4.13's "finite cyclic" describes the maximal tower it constructs.

Linton uses this reading himself. Example 1.2 (p. 4) and Example 6.12 (p. 28) call a single
splitting with free vertex group "a one-relator hierarchy of length one". Example 1.2 then
applies Theorem 7.1 to it.

## Step 3: Theorem 7.1

Assume `sZ(psi_i) < infinity` and `sZ(psi_i^-1) < infinity` for all `i < N`. Checking both
directions makes the argument independent of orientation conventions. Then the hierarchy is
Z-stable (Definition 1.1).

Assume also that `G = pi_1(X_0)` has no Baumslag–Solitar subgroup. This holds when `G` is
hyperbolic, since `BS(m, +-m)` contains `Z^2` and `BS(m, l)` with `|m| != |l|` contains a
distorted infinite cyclic subgroup.

Theorem 7.1 (3)⇒(1) then shows that `G` is hyperbolic with a quasi-convex hierarchy, and that
`G` is virtually special, via Wise, Theorem 13.3. In particular `G` is linear over `Z`,
residually finite, and sofic.

**How the induction in Theorem 7.1 uses the pieces (p. 31).**
- The inductive hypothesis is applied to the shorter hierarchy `X_N -> ... -> X_1`.
  - It is again Z-stable.
  - `pi_1(X_1)` has no BS subgroup, being a subgroup of `G`.
- The base case (`N = 0`, `pi_1` a free product of cyclic groups) is the one Linton calls
  clear. Here `pi_1(X_N)` is free, so it is hyperbolic and virtually special, and every finitely
  generated subgroup is quasi-convex.

So the terminal free vertex group is covered.

## Scope

This is a statement about Linton's definitions applied to explicit complexes. It uses no
computation. `lintongraph.py` is listed only because the certificates that use this lemma compute
the `sZ` values with it.
