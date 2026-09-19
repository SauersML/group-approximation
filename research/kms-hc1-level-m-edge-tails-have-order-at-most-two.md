---
rg: 2
id: kms-hc1-level-m-edge-tails-have-order-at-most-two
kind: claim
title: The rho-visible tails of the A~2 edge relators have order at most two, and order two only on the diagonal shift (p-1)(e_x+e_y); so the (2p,2,2p) slice carries no level-2 jump, the level-m value localizes to nine edge slices, and the Kassel p-map of every t^m-homogeneous element has z-part alpha of its Cartan part
distinct_from:
  kms-hc1-witt-carry-syzygy-lifts-by-right-freeness: that claim proves the level-1 lift for every p >= 5 and proposes the (2p,2,2p) slice with second-order seeds f2 for level 2. This claim proves those seeds vanish under rho, so that slice is empty, and replaces it by the first-order slices (2p,p+1,2p) and the diagonal slices (p+1,p+1,2p).
  kms-hc1-witt-carry-syzygy-kassel-coordinate-vanishes: that claim uses the p-map of t X for square-zero X at level 1. This claim proves the z-part formula for every t^m-homogeneous X and every m >= 1, with no square-zero hypothesis.
  kms-hc1-edge-s-pair-jumps-are-affine-coroot-p-power-relations: that claim evaluates first-order tails f1 at (p,p,p). This claim bounds the tails of every order and every level, and shows the second-order tail is purely diagonal.
artifacts:
  - experiments/kms-hc1-level-m-tails-2026-09-18/heis_defect.py
  - experiments/kms-hc1-level-m-tails-2026-09-18/heis_defect_p5.out
  - experiments/kms-hc1-level-m-tails-2026-09-18/heis_defect_p7.out
  - experiments/kms-hc1-level-m-tails-2026-09-18/heis_defect_p11.out
  - experiments/kms-hc1-level-m-tails-2026-09-18/hilb.py
---

Notation of `kms-hc1-edge-s-pair-jumps-are-affine-coroot-p-power-relations`
(below: the edge-jump claim) and
`kms-hc1-witt-carry-syzygy-lifts-by-right-freeness` (below: the lift
claim). Fix a prime `p >= 5`.

- `A = F_p<<Y_a,Y_b,Y_c>>` with `Y_x = log(1+X_x)`. So the torus
  `(F_p^*)^3` acts by scaling the `Y_x`, and every torus eigencomponent `f`
  of a relator is a sum of homogeneous parts in multidegrees congruent mod
  `p-1`.
- `rho : A -> u(N)`, `Y_a -> E12`, `Y_b -> E23`, `Y_c -> E31 t`, where
  `N = N_(kappa,alpha)` is the Kassel extension of `L_p`. The map `rho` is
  multigraded.
- For an edge `{x,y}`, `h_xy` is the Heisenberg subalgebra of `N` spanned by
  `rho(Y_x)`, `rho(Y_y)` and their bracket `e_xy`. Its restricted enveloping
  algebra `u(h_xy)` has PBW basis `x^i e^k y^j` with `0 <= i,k,j < p`.
- An edge relator is `r = [[x,y],x]` or `[[x,y],y]` (group commutators).
  Put `D_r = r(E(rho Y_x), E(rho Y_y)) - 1` in `u(h_xy)`, where `E` is the
  truncated exponential. It is `rho(r-1)`, and for a torus class `c` in
  `[1,p-1]^2` the class-`c` part `D_r[c]` of `D_r` equals `rho(f)` for the
  eigencomponent `f = f_r{c}`.
- The **shift** of a `rho`-visible bidegree `d` of `f_r{c}` is
  `s = (d - c)/(p-1)`. The order of a tail is `s_x + s_y`.
- `W_m` is the level-`m` hidden space at `(mp,mp,mp)`, with coordinates
  `(kappa, alpha_A, alpha_B)`.

## Statement

> **(T1) Tail bound.** For every edge relator `r` and class `c`, every
> `rho`-visible bidegree of `f_r{c}` has shift in `{0,1}^2`. So tails have
> order at most 2. The only possible order-2 tail is the diagonal shift
> `(p-1)(e_x+e_y)`, and a single-letter shift of `2(p-1)` is never visible.

> **(T2) Shape.** For every `p` in `{5, 7, 11}` and every class, the shifts
> that occur are exactly these. For `[[x,y],x]` they are `(0,1)` and
> `(1,1)`. For `[[x,y],y]` they are `(1,0)` and `(1,1)`. The shift `(0,0)`
> never occurs, so lowest forms are `rho`-invisible. Diagonal components are
> nonzero in many classes. For example, at `p=5` the class `(2,1)` of
> `[[a,b],a]` is visible exactly in `(2,5)` and `(6,5)`.

> **(T3) The proposed level-2 slice is empty.** `u(N)` is zero in
> multidegrees `(2,2p-1,0)` and `(0,2p-1,2)`. So the second-order seeds
> `f2` of `f_[a,b,a]{210}` and `f_[b,c,c]{012}` have `rho(f2) = 0`. No term
> of an element of `I` whose overlap lies in the slice `(2p,2,2p)` can have
> a `rho`-visible part in `(2p,2p,2p)`.

> **(T4) Nine-slice localization, every m.** Let `T = sum c_i u_i g_i v_i`
> be in `I`, with `u_i`, `v_i` words and each `g_i` an eigencomponent of an
> edge relator, a `p`-power `Y_x^p`, or `(Y_xY_y - Y_yY_x)^p`. Then the
> `(mp,mp,mp)` part of `rho(T)` is a sum over the terms whose overlap
> multidegree `deg u_i + deg g_i + deg v_i` equals `(mp,mp,mp)` minus one of
> `(p-1)e_x`, `(p-1)e_y` or `(p-1)(e_x+e_y)`, where `{x,y}` is the term's
> edge. By (T2), the single-letter shift of a term is the one allowed by its
> relator type.
>
> - For `m=2` the live slices are the three first-order slices of the form
>   `(2p,p+1,2p)` and the three diagonal slices of the form `(p+1,p+1,2p)`.
>   That is six slices and nine (edge, shift) pairs.
> - For `m=1` no diagonal slice can occur.
> - No level uses a tail of order at least 3.

> **(T5) Level-m Kassel p-map.** For every `m >= 1`, every `p >= 3` and
> every `X` in `sl3`, the `z`-part of `(X t^m)^[p]` in `N` equals
> `sum_i c_i alpha(h_i)`, where `sum_i c_i h_i` is the Cartan part of `X` and
> `c_i` is in `F_p`. There is no square-zero hypothesis. The formula fails
> for elements that are not `t`-homogeneous.

## Proof idea

Full proofs are in `kms-hc1-level-m-edge-tails-have-order-at-most-two-proof`.

- **(T1).** `rho(f)` lies in `u(h_xy)`, where every basis element
  `x^i e^k y^j` has `x`-degree `i+k <= 2p-2`. Every monomial of `r-1`
  involves both letters, because `r` is trivial when either letter is set to
  1. So every visible degree `d_x` lies in `[1, 2p-2]` and is congruent to
  `c_x`, with `c_x` in `[1,p-1]`. That leaves `d_x` in `{c_x, c_x+p-1}`.
- **(T2).** This is an exact computation of `D_r` in `u(h)` at
  `p = 5, 7, 11` (`heis_defect.py`). Since `rho` is graded,
  `D_r(E(lambda x), E(mu y))` is the torus translate. So the class-`c` part
  of `D_r` is exactly `rho(f_r{c})`.
- **(T3).** In c-degree 0 the only generators of `u(N)` of positive degree
  are `E12`, `E23` and `E13`. A b-degree of `2p-1` would need
  `E23^j E13^k` with `j+k = 2p-1`, but `j,k <= p-1`. In a-degree 0 and
  c-degree 2, the b-degree comes from `E23^j (E21 t)^k` with `k <= 2`. So
  `j >= 2p-3 >= p`, and that product is also zero. A visible jump by a
  b-shift from b-degree 2 to `2p` needs shift `2(p-1)`, which (T1) rules
  out.
- **(T4).** `rho(u g v) = rho(u) rho(g) rho(v)`, and the following vanish
  under `rho`:
  - the Serre lowest forms (the Serre relations hold in `N`);
  - `Y_x^p` (root vectors have p-map 0);
  - `(Y_xY_y - Y_yY_x)^p` (edge commutators have p-map 0).

  So only visible tails of eigencomponents contribute, and (T1) lists their
  shifts. At `m=1` a diagonal slice `(1,1,p)` would need an edge
  eigencomponent of total `xy`-degree 2. But edge relators start in degree
  3.
- **(T5).** Take `W = lambda u + v` with `u = Y t^m` and `v = X t^m`. The
  Jacobson term `s(u,v)` is read off from `ad(W)^(p-1)(u) = [W, R]`, where
  `R = ad(W)^(p-2)(u)` lies in `sl3 t^(m(p-1))`. Inner brackets contribute
  only central terms, and `ad` of a central term is 0. So the `z`-part is
  `m kappa tr(W R) = m kappa tr([W,W] ad(W)^(p-3) u) = 0`, by invariance of
  the trace form. Hence the `z`-part of `(u+v)^[p]` is additive. The
  formula follows from the p-map on root vectors (0) and on `h t^m` (whose
  `z`-part is `alpha(h)`), using p-semilinearity over `F_p`.
  Inhomogeneous `W` pairs different `t`-degrees in the cocycle, and the
  argument breaks.

## Status

- **Proved, every p >= 5:** (T1), (T3), (T4), (T5).
- **Checked exactly:** (T2) at `p = 5, 7, 11`, for all classes of both
  relator types (`heis_defect_p*.out`). A general-`p` proof of (T2) is not
  written.
- **Refutes** the route proposed in the lift claim: the `(2p,2,2p)` slice
  with seeds `f2` is empty. The level-2 hidden directions have to come from
  first-order jumps out of `(2p,p+1,2p)`-type slices, or from diagonal
  second-order tails out of `(p+1,p+1,2p)`-type slices.
- **Caveat.** `gr I` is graded only mod `p-1`. So an element of `I` whose
  value lands at `(2p,2p,2p)` must also have its lower multidegrees of total
  degree `6p` in `gr I`. The level-2 analogue of (R1) of the edge-jump claim
  is needed, and it is not proved here.

## Next step

Compute, at `p=5`, the S-pairs of the slices `(2p,p+1,2p)` (first order,
edges `ab` and `bc`) and `(p+1,p+1,2p)` (diagonal, edge `ab`), up to
rotation. This is the level-2 analogue of `fo_sb.cpp`, with tails of
order `<= 2` carried as `rho`-images in `u(N)` truncated at `(10,10,10)`.
The box `(10,6,10)` has PBW dimension 23170 at its top (`hilb.py`).

Then test whether the values span the 3-dimensional `W_2`. By (T5), the
level-1 conjugation argument of the Kassel claim transfers to `t^2`
conjugators such as `E23 t`. One more route should be checked alongside:
products of level-1 elements of `gr I` at `(p,p,p)` with words of
multidegree `(p,p,p)`.
