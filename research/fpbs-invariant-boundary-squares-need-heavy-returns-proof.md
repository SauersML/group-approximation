---
rg: 2
id: fpbs-invariant-boundary-squares-need-heavy-returns-proof
kind: route
title: A returning boundary pair has its geodesic pass near o and near g^{-1}o, so one endpoint is expanded out of a thin shadow and the other contracted into one; invariance bounds the contracted self-return by the shadow mass, bounded shadow multiplicity bounds each sphere sum, and Hoelder at each sphere leaves only the sphere maxima
target: fpbs-invariant-boundary-squares-need-heavy-returns
requires:
  - fpbs-finite-fibre-bb-classes-are-boundary-squares
  - fpbs-dini-boundary-class-diagonal-dissipative
---

Full written proof. Notation is as in the target claim. All sets are Borel.

## Imported inputs

- **(I1) Hyperbolic geometry.** For `x, y` in `Gamma ∪ dGamma`, `(x|y)_o` is the Gromov product. A bi-infinite
  geodesic `l` from `eta` to `xi` passes within `(xi|eta)_o + c delta` of `o`. If `p` lies within `r` of `l`, then
  `(xi|p)_o >= d(o,p) - r - c delta` when `p` lies on the `xi` side of the point of `l` nearest `o`, at distance
  `> r + c delta` from it. Here `c` is a universal constant.
- **(I2) Bounded shadow multiplicity.** For `D >= 0` there is `M = M(D, delta)` such that each `zeta in dGamma` lies in
  `Sh_D(g)` for at most `M` elements `g in S_n`, for every `n`. (Such `g` lie within `D + c delta` of the point at
  distance `n` on a geodesic ray from `o` to `zeta`, and balls of fixed radius have bounded cardinality.)
- **(I3) Conservativity.** For a measure-preserving action on a sigma-finite space and a set `E` of finite measure
  contained in the conservative part, a.e. point of `E` returns to `E` infinitely often. Integrating gives
  `sum_g m(E cap g^{-1}E) = infinity` (as in the proof of `fpbs-finite-fibre-bb-classes-are-boundary-squares`).

## Proof of Lemma 1

Let `D_0 = max_{(xi,eta) in K1 x K2} (xi|eta)_o + c delta`. This is finite since `K1`, `K2` are compact and disjoint.
Let `(xi, eta) in K1 x K2` with `(g xi, g eta) in K1 x K2`, and let `l` be a geodesic from `eta` to `xi`. By (I1),
`l` passes within `D_0` of `o`. The geodesic `g l` joins `g eta` to `g xi`, so it also passes within `D_0` of `o`.
Applying `g^{-1}`, `l` passes within `D_0` of `g^{-1} o`. Let `p_0`, `p_1` be points of `l` within `D_0` of `o` and of
`g^{-1}o`. Then `d(p_0, p_1) >= |g| - 2 D_0`. Take `n_0 = 4 D_0 + 4 c delta`.

*Case (i): `p_1` lies on the `xi` side of `p_0`.* By (I1) with `r = D_0`, `(xi|g^{-1})_o >= |g| - D` with
`D = 2 D_0 + c delta`. So `xi in Sh_D(g^{-1})`. Apply `g`: the line `g l` passes within `D_0` of `g p_1` (near `o`)
and of `g p_0` (near `g o`). Along `g l`, which runs from `g eta` to `g xi`, the point `g p_0` lies on the `g eta` side
of `g p_1`, because `p_0` lies on the `eta` side of `p_1`. By (I1) again, `(g eta | g)_o >= |g| - D`, so
`g eta in Sh_D(g)`.

*Case (ii): `p_1` lies on the `eta` side.* The same argument with `xi` and `eta` exchanged gives
`eta in Sh_D(g^{-1})` and `g xi in Sh_D(g)`. Since `d(p_0,p_1) > 0` once `|g| >= n_0`, one of the cases holds. ∎

## Proof of Theorem 2

Write `A = A1 x A2` and `m = lambda x lambda`. Then
`R(A) = sum_g m(A cap g^{-1}A)`. Split the sum at `|g| = n_0`. The short part has at most `|B(n_0)|` terms, each at
most `m(A) = lambda(A1) lambda(A2)`, which gives `C_0`.

For `|g| >= n_0`, a point `(xi,eta)` of `A cap g^{-1}A` has `xi in A1`, `g xi in A1`, `eta in A2`, `g eta in A2`. By
Lemma 1 it is of type (i) or (ii). Type (i) points lie in
`[A1 cap g^{-1}A1 cap Sh_D(g^{-1})] x [A2 cap g^{-1}(A2 cap Sh_D(g))]`,
whose `m`-measure is `a_g b_g`. Type (ii) points give `a'_g b'_g` in the same way. This proves the first inequality.

*Sphere sums.* Since `a_g <= lambda(A1 cap Sh_D(g^{-1}))` and inversion maps `S_n` onto itself,
`sum_{g in S_n} a_g <= sum_{h in S_n} lambda(A1 cap Sh_D(h)) = int_{A1} #{h in S_n : zeta in Sh_D(h)} d lambda(zeta)
<= M lambda(A1)` by (I2). For `b_g`, invariance of `lambda` gives
`b_g <= lambda(g^{-1}(A2 cap Sh_D(g))) = lambda(A2 cap Sh_D(g))`, and (I2) gives `sum_{S_n} b_g <= M lambda(A2)`.
The primed quantities are the same with `A1`, `A2` exchanged. ∎

*Remark (where invariance enters).* If `lambda` were only quasi-invariant, `lambda(g^{-1}(A2 cap Sh_D(g)))` would be
`int_{A2 cap Sh_D(g)} (d g^{-1}_* lambda / d lambda)`, and the derivative of the expanding map `g^{-1}` on a thin shadow
of `g` is of size `e^{Theta(n)}` for positive-dimensional classes. The sphere bound for `b_g` would then fail.

## Proof of Theorem 3

For each `n >= n_0`: `sum_{S_n} a_g b_g <= (max_{S_n} b_g) sum_{S_n} a_g <= M lambda(A1) beta_n`, and
`sum_{S_n} a'_g b'_g <= (max_{S_n} a'_g) sum_{S_n} b'_g <= M lambda(A1) alpha'_n` (here `b'_g` is the contracted
self-return of `A1`, so its sphere sum is at most `M lambda(A1)`). Summing over `n` and using Theorem 2 gives the first
bound. The second bound is the same with the other factor pulled out at each sphere.

Suppose now that the conservative part `Con` of `(d^2 Gamma, m)` meets `A` in positive measure. Put `E = A cap Con`.
By (I3), `R(E) = infinity`. Since `E ⊂ A`, `R(A) >= R(E) = infinity`. Both bounds then force the stated divergences. ∎

## Proof of Corollary 4

1. The inequalities `a_g <= lambda(A1 cap Sh_D(g^{-1}))` and `b_g <= lambda(A2 cap Sh_D(g))` were shown above. If
   `omega_2(n) = max_{g in S_n} lambda(A2 cap Sh_D(g))` is summable, then `sum beta_n < infinity`. If the same holds
   for `A1`, Theorem 3 gives `R(A) < infinity`.
2. Suppose `beta_{n_k} >= c > 0` along `n_k -> infinity`, attained at `g_k in S_{n_k}`. Then
   `lambda(A2 cap Sh_D(g_k)) >= c`. The shadows `Sh_D(g_k)` have visual diameter at most `C e^{-epsilon n_k}` and meet
   the compact set `K2`. Pass to a subsequence along which they converge to a point `zeta`. For each `r > 0`,
   `lambda(A2 cap B(zeta, r)) >= c` for large `k`. Since `lambda|_{A2}` is finite, continuity from above gives
   `lambda(A2 cap {zeta}) >= c`, an atom. The same argument applies to `alpha_n`, `alpha'_n` and `beta'_n`.
3. Let `lambda` be counting measure on the invariant countable set `Gamma h^+ ∪ Gamma h^-`. Take `A1 = {h^+}` and
   `A2 = {h^-}`, which have disjoint closures. For
   `g = h^{-k}`, `g h^+ = h^+` and `g h^- = h^-`. For large `k`, `h^+ in Sh_D(h^k) = Sh_D(g^{-1})` and
   `h^- in Sh_D(h^{-k}) = Sh_D(g)`, so `a_g = b_g = 1`. The point `(h^+, h^-)` has infinite stabiliser, so it returns
   infinitely often, and the orbit `Gamma (h^+, h^-)` with counting measure is conservative.
4. For a measure-preserving `T` and `A` of finite measure,
   `sum_{|k| = n} m(A cap T^k A) = 2 m(A cap T^n A) <= 2 m(A)`. This is the budget of Theorem 2, with `M = 2`. Both
   outcomes occur for `Z`: Kakutani--Parry (1963) exhibit infinite Markov shifts with `T x T` conservative, and others
   with `T x T` totally dissipative. So no bound that depends only on sphere sums and sphere maxima of the self-return
   masses can separate the two outcomes. This item is a remark about methods and is not used elsewhere. ∎

## Status

Lemma 1, Theorems 2 and 3 and Corollary 4.1--4.3 are complete proofs. Corollary 4.4 is a calibration remark with a
classical citation. The square problem (II_inf-square) and the statement (heavy-pair) remain OPEN.
