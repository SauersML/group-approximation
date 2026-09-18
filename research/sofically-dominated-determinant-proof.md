---
rg: 2
id: sofically-dominated-determinant-proof
kind: route
title: Embed the group ring trace-preservingly in the orbit relation, compare determinants by operator monotonicity of log, and bound the dominated element by Elek--Lippner
target: sofically-dominated-integral-matrices-obey-determinant
requires:
  - determinant-conjecture-holds-for-sofic-groups
---

Direct proof (2026-09-17, lane sw-047). Notation as in the target.

**External inputs.**
- **(EL)** G. Elek and G. Lippner, *Sofic equivalence relations*, J. Funct.
  Anal. 258 (2010), arXiv:0906.3619: sofic measured relations satisfy the
  measurable determinant conjecture, `det_N(R')(A) >= 1` for
  `A in M_(m x n)(ZR')`; treeable relations are sofic. Read from source in
  `research/artifacts/unimodular-networks-mdc-2026-09-12.md`, Section 0.
- **(ES)** Elek--Szabó, the sofic group case
  (`determinant-conjecture-holds-for-sofic-groups`).
- **(M)** `log` is operator monotone on `(0, infinity)`.
- **(K)** Kesten: the simple random walk on the `2d`-regular tree has spectral
  radius `sqrt(2d-1)/d`, so the Cayley Laplacian of a free group of rank `d`
  has bottom of spectrum `2d - 2 sqrt(2d-1)`. For `d = 3` this is
  `6 - 2 sqrt 5 ≈ 1.528`.

## Step 1: traces

- For an essentially free action, `g -> chi_(graph of g)` embeds `Z[G]` in
  `ZR` with `tr(g) = mu(Fix g) = [g = e]`, the group trace. Taking matrices,
  `M_n(Z[G])` embeds in `M_n(ZR) = ZR^(n)` with the same trace.
- For a subrelation `R' <= R^(n)` on the same space, `ZR'` sits in `ZR^(n)`
  with the same trace `tr(f) = integral f(p,p) dp`.
- Spectral measures of self-adjoint elements are determined by trace moments.
  So `mu_T` is the same in `N(G)` and `N(R^(n))`, `mu_S` is the same in
  `N(R')` and `N(R^(n))`, and the determinants agree. (Normalizing the measure
  on `X x [n]` to a probability only rescales `log det` by `1/n`.)

## Step 2: monotonicity

Work in the finite von Neumann algebra `M = N(R^(n))` with faithful normal
trace `tr`. Let `0 <= S <= T` and `eps > 0`.
- By (M), `log(S + eps) <= log(T + eps)`, so
  `integral log(lambda + eps) d mu_S <= integral log(lambda + eps) d mu_T`.
- As `eps -> 0`, `log(lambda + eps)` decreases to `log lambda`, bounded above
  by `log(||T|| + 1)` on the spectra. The measures are finite, so monotone
  convergence gives
  `integral_[0,infinity) log lambda d mu_S <= integral_[0,infinity) log lambda d mu_T`
  in `[-infinity, infinity)`.
- `ker S = 0` and `tr` is faithful, so `mu_S({0}) = 0` and the left side is
  `log det_M(S)`.
- If `Tf = 0` then `<Sf, f> <= <Tf, f> = 0`, so `S^(1/2) f = 0` and `f = 0`.
  Hence `ker T = 0`, `mu_T({0}) = 0`, and the right side is `log det_M(T)`.

## Step 3: conclusion

By (EL) applied to `S in ZR'`, `log det_N(R')(S) >= 0`. By Steps 1 and 2,
`log det_N(G)(T) = log det_M(T) >= log det_M(S) = log det_N(R')(S) >= 0`.

**Subgroup form.** `Z[H] <= Z[G]` is trace-preserving, so
`det_N(G)(S) = det_N(H)(S) >= 1` by (ES). Step 2 in `N(G)` finishes. ∎

## Corollary: diagonally dominant matrices, infinite part

Notation as in `diagonally-dominant-determinant-spanning-forest-proof`:
`T_inf` on types `I_inf`, the graph `X_inf`, its wired uniform spanning forest
`F` (automorphism-invariant, all trees infinite), and
`S_F = sum_(edges of F) u_vw u_vw^*`, `u_vw = 1_v + eps_vw 1_w`.
- **Space.** `Omega` = forests of `X_inf` with the WUSF law (independent on
  components), times `[0,1]^G` with product measure. `G` acts diagonally. The
  law is invariant and the Bernoulli factor makes the action essentially free.
- **Subrelation.** On `Omega x I_inf`, relate `(omega, i)` to
  `(h^(-1) omega, j)` when `(h, j)` lies in the tree of `F(omega)` through
  `(e, i)`. Translation covariance `F(h^(-1) omega) = h^(-1) F(omega)` makes
  this an equivalence relation contained in `R^(|I_inf|)`. The forest edges
  form a Borel treeing, so `R'` is treeable, hence sofic by (EL).
- **The element.** `S_F` has entries `±1` on forest edges and `deg_F` on the
  diagonal, so it lies in `ZR'`.
- **Domination.** `T_inf - S_F` is a sum of positive rank-one terms on the
  remaining weight and the nonnegative diagonal `W` (Step 4 of that proof), at
  every `omega`. So `0 <= S_F <= T_inf` in the direct integral.
- **Injectivity.** At each `omega`, `<S_F f, f> = sum_(edges) |f(v) + eps f(w)|^2`.
  If this is `0`, `|f|` is constant on each tree. Trees are infinite, so
  `f in l^2` forces `f = 0`. Hence `ker S_F = 0` in `N(R^(|I_inf|))`.

The theorem gives `det T_inf >= 1`, and the finite part is Step 2 of the
spanning-forest proof. Neither Lyons' tree-entropy bound nor the gauge is used.

## Corollary: Laplacian minus a constant

Let `K = <s_i : i in A>` and `H = <s_i : i in B>`.
- **Gap transfers from `K` to `G`.** `Delta_A` acts by right convolution with
  an element of `Z[K]`. It preserves each `l^2(gK)`, and on each coset it is
  unitarily equivalent to its action on `l^2(K)`. So
  `Delta_A >= lambda_0(Delta_A) >= c` on `l^2(G)`.
- **Domination.** `Delta - c = (Delta_A - c) + Delta_B >= Delta_B >= 0`.
- **Injectivity.** If `Delta_B f = 0` then
  `sum_(i in B) ||f - f s_i||^2 = 0`, so `f` is constant on each coset `gH`.
  Cosets are infinite, so `f = 0`.
- **Soficity.** `Delta_B in Z[H]` with `H` sofic. The subgroup form applies.

**Example.** With `A = {a, b, c}` free of rank 3 and `B = {g}`, (K) gives
`lambda_0 = 6 - 2 sqrt 5 > 1`, so `Delta_(a,b,c,g) - 1` obeys the conjecture over
every such `G`. The element is `7 - sum_(s in {a,b,c,g}) (s + s^-1)`: its
coefficient at `e` is `7` and its off-diagonal absolute mass is `8` (also when
`g = a`, where it reads `7 - 2(a + a^-1) - (b + b^-1) - (c + c^-1)`). So it is
not diagonally dominant.

## Remark: square row restriction

For `B in M_n(Z[G])` and a row projection `P_H` in `N(R^(n))`, injectivity of
`B^* P_H B` gives injectivity of `P_H B`. In a finite von Neumann algebra the
support and range projections of an operator have equal trace, so
`n = tr(range proj of P_H B) <= tr(P_H) <= n`, and `P_H = 1` by faithfulness.
