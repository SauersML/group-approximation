---
rg: 2
id: product-with-divisible-cantor-action-kills-finite-type-proof
kind: route
title: Lifting equidecompositions from the factors to rectangles gives a paradoxical decomposition of the product unit
target: product-with-divisible-cantor-action-kills-finite-type
requires: []
---

Type semigroups: clopen subsets of `Z x N` up to equidecomposition by clopen
pieces moved by group elements, with label changes; `[C] <= [D]` means `C` is
equidecomposable with a subset of `D`.

**Step 1 (lifting along rectangles).**  For a clopen `Z0 subset Y` and clopen
`C subset X x N` write `C (x) Z0 = {(x, z, i) : (x, i) in C, z in Z0}`.  If
`C <= D` in `S(X, Gamma)` via pieces `A_k subset C`, elements `g_k` and label
changes `i_k -> j_k`, then the pieces `A_k (x) Z0`, moved by `(g_k, 1)` with
the same label changes, show `C (x) Z0 <= D (x) Z0` in `S(X x Y, Gamma x H)`.
If `Z0 ~ Z1` in `S(Y, H)` via pieces `P_l` and `h_l`, then the pieces
`C (x) P_l` moved by `(1, h_l)` show `C (x) Z0 ~ C (x) Z1`.

**Step 2.**  Put `v = [X (x) V]` and `w = [X (x) W]`.  By Step 1,
`[1_{X x Y}] = 2v + 3w`.  Also `2v = [(X x {0,1}) (x) V]` and
`4v = [(X x {0,1,2,3}) (x) V]`, so the relation `4[1_X] <= 2[1_X]` lifts to
`4v <= 2v`; likewise `4w <= 2w`.

**Step 3.**  Let `p = 2v + 2w` and `q = w`.  Then `2p <= p`, and
`q <= 2w <= p`.  Hence `[1] = p + q <= 2p <= p <= [1]`, and
`2[1] = 2p + 2q <= 4p <= p <= [1]`.  So `[1_{X x Y}]` is properly infinite.

**Step 4.**  A properly infinite unit class gives clopen-piecewise partial
isometries `s, t` in `C(X x Y) rtimes_r (Gamma x H)` with `s*s = t*t = 1` and
orthogonal ranges (Rainone, arXiv:1502.06153, Proposition 4.17 direction).
The reduced crossed product of a product action is the minimal tensor product
of the two reduced crossed products.

**Towers.**  For a minimal `Z`-action on a Cantor space choose a clopen base
`C` small enough that every return time is at least 2; the Kakutani--Rokhlin
tower over each return-time piece `C_i` has height `h_i >= 2`.  Write
`h_i = 2s_i + 3t_i` and group consecutive levels `T^j C_i` into pairs and
triples.  The first and second members of pairs give `V, V'` (moved by `T`),
and the members of triples give `W, W', W''` (moved by `T`, `T^2`).

**Product properties.**  Orbits of `(x, y)` are `Gamma x times H y`, dense when
both actions are minimal.  If `(g, h) != 1` fixes a rectangle `U x U'`
pointwise, then `g` fixes `U` and `h` fixes `U'`, contradicting topological
freeness of a factor.  An invariant measure on `X x Y` pushes forward to one
on `X`.
