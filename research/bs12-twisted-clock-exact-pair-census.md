---
rg: 2
id: bs12-twisted-clock-exact-pair-census
kind: claim
artifacts:
  - experiments/bs12-twisted-clock-census-2026-09-17/census.py
  - experiments/bs12-twisted-clock-census-2026-09-17/analyze.py
title: The Fourier-twisted clock pair (A_s, D) is at distance at least sin(s(1+cos(pi/N))) -> sin(2s) from exact BS(1,2) pairs with the same base, while exact pairs with moved base come strictly closer, with explicit distances decreasing in N
distinct_from:
  bs12-trivially-padded-opnorm-correction: that is the open correction statement (TPC, equivalent to ESS Q3); this is a sharpened fixed-base obstruction plus an explicit census of moved-base exact corrections on its sharp test family, and does not settle it.
  bs12-separated-doubling-spectra-correct-conjugators-unpadded: that corrects conjugators with the base fixed on separated spectra and records the |J_1(2s)|/2 fixed-base bound on this family; this improves that bound to sin(s(1+cos(pi/N))) and measures what moving the base buys.
---

**ESTABLISHED (items 1--2: elementary written proof; item 3: explicit exact
pairs produced by computation, their distances are floating-point evaluated
norms, not interval-certified).**

Notation.  `N` odd, `w = e^(2 pi i/N)`, `D e_j = w^j e_j`, `W e_j = e_(j/2 mod N)`,
`V e_j = e_(j+1)`, `H = V + V^*`, `A_s = W exp(isH)`.  Then `W D W^* = D^2`
and `||A_s D A_s^* - D^2|| = O(s/N)`.  Distances are operator norms.

1. **Fixed-base obstruction (sharpened).**  For `0 < s <= pi/4`, every
   unitary `C` with `C D C^* = D^2` satisfies
   `||C - A_s|| >= sin(s(1 + cos(pi/N)))`, which tends to `sin(2s)`.  The
   trivial correction `C = W` has `||W - A_s|| = 2 sin s`.  So the
   fixed-base distance lies in `[sin(s(1+cos(pi/N))), 2 sin s]`.  This
   replaces the bound `~|J_1(2s)|/2` recorded on
   `bs12-trivially-padded-opnorm-correction`; at `s = 1/2` it is `0.841`
   against `0.220`.
2. **What a moved base must do.**  If `(C, Z)` is exact with
   `||C - A_s|| <= a`, then for `k = (N-1)/2`,
   `||Z^k - D^k|| + ||Z^(2k) - D^(2k)|| >= 2 sin(s(1+cos(pi/N))) - 2a`.
   So every exact correction closer than `sin 2s` moves the high powers
   `Z^((N-1)/2)`, `Z^(N-1)` of the base by order one.  The first-order
   bound `||Z^k - D^k|| <= k ||Z - D||` says nothing here.  The
   obstruction is carried entirely by the near-antipodal powers.
3. **Census of moved-base exact corrections.**  `census.py` minimizes
   `max(||C - A_s||, ||Z - D||)` over all exact pairs with simple `N`-th-root
   base spectrum.  These are exactly `Z = U D U^*` and
   `C = U W diag(e^(i theta)) U^*` with `U` in `U(N)` arbitrary, since
   `{C : C D C^* = D^2} = W * (diagonal unitaries)`.  It uses Schatten-16
   and Schatten-32 surrogates with L-BFGS.  Each printed value is the true
   operator norm of a feasible pair, with relation error at most `2e-13`.
   So every entry is an upper bound for the distance `d(s,N)` from `(A_s, D)`
   to exact pairs in `U(N)`.

   | `s` | `N=9` | `27` | `45` | `81` | `135` | `189` | `243` | fixed-base floor `sin 2s` | `2 sin s` |
   |---|---|---|---|---|---|---|---|---|---|
   | 0.5 | 0.566 | 0.490 | 0.453 | 0.416 | 0.392 | 0.373 | 0.364 | 0.841 | 0.959 |
   | 0.25 | | 0.314 | | 0.277 | 0.273 | | 0.259 | 0.479 | 0.495 |
   | 0.1 | | 0.147 | | 0.142 | 0.135 | | 0.135 | 0.199 | 0.200 |

   The defect `||A_s D A_s^* - D^2||` is `0.23, 0.078, 0.047, 0.026` at
   `N = 27, 81, 135, 243` for `s = 0.5`, and scales linearly in `s`.

## Proofs of items 1 and 2

Write `f_m` for the Fourier basis, so that `V`, `H` and `exp(isH)` are
diagonal there: `H f_m = 2 cos(a_m) f_m` with `a_m = 2 pi m/N`.  From
`V e_j = e_(j+1)` and `D e_j = w^j e_j` we get `D V D^(-1) = w V`.  Hence
`D^(-k) H D^k = w^(-k) V + w^k V^* =: H'`, which is also Fourier-diagonal,
with eigenvalues `2 cos(a_m - 2 pi k/N)` on `f_m`.

*Item 1.*  Since `W D^k W^* = D^(2k)`,

`A_s D^k A_s^* - D^(2k) = W (e^(isH) D^k e^(-isH) - D^k) W^* = W D^k (e^(isH') - e^(isH)) e^(-isH) W^*`.

So `||A_s D^k A_s^* - D^(2k)|| = ||e^(isH') - e^(isH)|| = max_m |e^(2is cos(a_m - 2pi k/N)) - e^(2is cos a_m)|`.
Take `k = (N-1)/2`, so `2 pi k/N = pi - pi/N`, and evaluate at `m = 0`.
This gives `|e^(-2is cos(pi/N)) - e^(2is)| = 2 |sin(s(1 + cos(pi/N)))|`.

If `C D C^* = D^2`, then `C D^k C^* = D^(2k)`.  So

`||A_s D^k A_s^* - D^(2k)|| = ||A_s D^k A_s^* - C D^k C^*|| <= 2 ||A_s - C||`.

Therefore `||C - A_s|| >= |sin(s(1+cos(pi/N)))|`.  For `s <= pi/4` the
argument is at most `pi/2`, so the bound increases to `sin 2s` as
`N -> infinity`.  For the upper bound, `||W - A_s|| = ||1 - e^(isH)|| = max_m |1 - e^(2is cos a_m)|`.
This equals `2 sin s` at `m = 0` when `s <= pi/2`.  QED.

*Item 2.*  Now let `C Z C^* = Z^2` and `k = (N-1)/2`.  Using
`C Z^k C^* = Z^(2k)`,

`||A_s D^k A_s^* - D^(2k)|| <= ||A_s D^k A_s^* - C D^k C^*|| + ||C (D^k - Z^k) C^*|| + ||Z^(2k) - D^(2k)||`,

and the first term is at most `2a`.  Combine this with the value computed
in item 1.  QED.

## What the census shows (item 3)

- *Moving the base beats the fixed-base floor by a wide margin.*  At
  `s = 0.5` the census distance is `0.364` at `N = 243`.  That is below
  the fixed-base floor `0.841` and below the first-order level of about
  `1.5 s = 0.75` (see below), and it is still falling, roughly like `N^(-0.12)`.
  No plateau appears on `9 <= N <= 243`.  So at `s = 1/2` the census gives
  no evidence that `(A_s, D)` is an ESS Q3 counterexample.  The data are
  compatible with `d(1/2, N) -> 0`, slowly.
- *Shape of the optimal correction.*  `analyze.py` on the saved optima
  gives the following.
  - `U` is far from `1` and far from Fourier-diagonal:
    `||U - 1|| = 1.77, 1.92, 2.0` at `N = 81, 189, 243`.
  - The eigenvectors `U e_j` of the new base are localized in position.
    Their median spread is `4.9, 10.1, 12.7` sites, a window of about
    `0.05 N`.
  - `||Z - D||` is about `2 pi * 0.055`.

  So the optimum replaces the `N`-th-root clock by a clock blurred over a
  mesoscopic window.  This is the mechanism item 2 forces: the
  near-antipodal powers `D^((N-1)/2)` must move by order one, and blurring
  over `~ 0.05 N` sites does exactly that while moving `D` itself by only
  `O(0.05)`.
- *Small `s` is the unresolved regime.*  The ratio `d(s,N)/s` on
  `N = 27, 81, 135, 243` is:
  - `1.47, 1.42, 1.35, 1.35` at `s = 0.1`;
  - `1.26, 1.11, 1.09, 1.04` at `s = 0.25`.

  It decreases slowly.  The `s = 0.1` value repeats at `N = 243`, which may
  just be under-convergence of a single start.  These numbers do not tell a
  slow decay to `0` apart from a positive limit.
- *First-order comparison.*  Take the functional
  `Psi(X) = <f_0, W^* X f_0> - (1/2)(<f_(N/3), W^* X f_(N/3)> + <f_(2N/3), W^* X f_(2N/3)>)`,
  for `3 | N`.  It vanishes on `W * (diagonal)` and on `K - W^* K W`, and
  `|Psi(A_s)| = 2 sin(3s/2)`.  So corrections that are first order in
  `U - 1` cannot get below about `1.5 s`.  The census values `~ 1.35 s`
  at `s = 0.1` sit just under that level.  They use `U` far from `1`,
  which the first-order bound does not cover.

## Status and limits

- Items 1 and 2 are complete proofs.
- Item 3 gives upper bounds only.  They come from one optimizer start per
  large `N`, the optimization is probably under-converged, and the
  distances are not interval-certified.
- The census covers only exact pairs whose base has simple `N`-th-root
  spectrum in `U(N)`.  Exact pairs with other base spectra, or in larger
  dimension, are not searched.  So item 3 never gives lower bounds for
  `d(s,N)`.
- It does not decide TPC / ESS Q3, and
  `bs12-trivially-padded-opnorm-correction` stays OPEN.

**Precise OPEN question isolated here.**  Is there a fixed `s > 0` with
`liminf_(N->inf, N odd) d(s,N) > 0`, where `d` is the distance to all
exact pairs in `U(N)`?  The defect is `O(s/N) -> 0`, so a positive answer
for a single `s` refutes ESS Q3 (same-dimension stability of `BS(1,2)`).
The other outcome would be a proof that `d(s,N) -> 0` for every `s`, which
removes this family as a candidate counterexample.  The census points to
the second option at `s = 1/2`, where `d` keeps decreasing.  At small `s`,
where `d/s` is nearly flat on the range computed, it decides nothing.
