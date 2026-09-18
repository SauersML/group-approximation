---
rg: 2
id: torus-dipole-covers-rank-distance-linear-in-profile-proof
kind: route
title: Cutting the row circle of the shortest lattice direction at the two charges, regluing each arc into a torus, and cancelling the seam charges along a digital line of lambda_1 squares costs 6 |A| lambda_1
target: torus-dipole-covers-rank-distance-linear-in-profile
requires: []
---

Notation as in the claim. We also cite the following from `torus-abelian-covers-rectangle-profile-near-commute-proof`:
- Lemma 5 (moves) and Lemma 6 (tree cancellation);
- the lower bound of its Section 5, `rho >= |A| ceil(m_0/2)/2` with `m_0 = min(|g|_1, lambda_1)`.

That lower bound is proved there in full. For permutations, `rank(p - q)` is at most the number of points where
`p` and `q` differ.

**Sites.** A *site* is a pair `(x, b)` or `(x, c)` with `x in G`. A permutation of `Omega` that agrees
with `b` off the fibre `{x} x A` differs from `b` in rank at most `|A|`. So if `(b'', c'')` differs
from `(b, c)` on the fibres over at most `M` sites in total, then `max(rank(b''-b), rank(c''-c)) <= |A| M`.

## 1. A short lift

**Lemma 1.** Let `w = k v` in `Lambda` with `v` primitive. For any `z in Z^2` there is an integer `m` with
`|z + m w|_2 <= |det(v,z)|/|v|_2 + |w|_2/2`.

*Proof.* Put `n = (-v2, v1)`, so that `det(v, n) = |v|_2^2`. Write
`z = alpha v + (det(v,z)/|v|_2^2) n`. Choose `m` with `|alpha + m k| <= k/2`. Then
`z + m w = (alpha + m k) v + (det(v,z)/|v|_2^2) n`. The two components are orthogonal, with norms at
most `k|v|_2/2 = |w|_2/2` and `|det(v,z)|/|v|_2`. QED.

## 2. Rows and pieces

Fix a shortest `w = k v` (in `l^1`) of `Lambda`, so `lambda_1 = |w|_1 = k|v|_1`, with `v` primitive. Let
`l = |v|_inf`, and choose `u` with `det(v,u) = 1`. Note `det(v, e1) = -v2` and `det(v, e2) = v1`.

**Rows.**
- *`Lambda ∩ Z v = Z w`.* This lattice is `Z j v` for some `j`, and `j` divides `k`. Minimality of `w`
  forces `j = k`.
- *`det(v, Lambda) = L Z` with `L = N/k`.* The map `z -> det(v,z)` is onto `Z` with kernel `Z v`. So
  `N = [Z v : Lambda ∩ Z v] [Z : det(v, Lambda)] = k [Z : det(v,Lambda)]`.
- Hence the row index `r(x) = det(v, z) mod L` (for any lift `z` of `x`) is well defined on `G`.

**Pieces.** Let `I = {s, s+1, ..., s+H-1}` be a cyclic interval of `Z/L` with `2l <= H < L`. Let
`P_I = r^-1(I)`, fix an integer lift `s'` of `s`, and put:
- `Sigma = {z : s' <= det(v,z) < s'+H}`;
- `Lambda_H = <w, H u>`;
- `T_I = Z^2/Lambda_H`.

**Lemma 2.**
- (a) The projection `Sigma -> G` induces a bijection `Sigma/Zw -> P_I`. The projection `Sigma -> T_I`
  induces a bijection `Sigma/Zw -> T_I`. Write `phi : P_I -> T_I` for the composite.
- (b) Put `nb(x) = phi^-1(phi(x) + e1)` and `nc(x) = phi^-1(phi(x) + e2)`. These are commuting permutations of `P_I`.
- (c) `nb(x) = x + e1` in `G` except at a set `R_b(I)` of exactly `k|v2|` points, and
  `nc(x) = x + e2` except at a set `R_c(I)` of exactly `k|v1|` points. So there are `lambda_1`
  redirects per piece.
- (d) Every point of `R_b(I) ∪ R_c(I)` has *relative height* `t = det(v, z) - s'` (with `z` its lift in
  `Sigma`) in `[0, l) ∪ [H - l, H)`.

*Proof.* (a) Surjectivity onto `P_I`: a lift `z` of `x` has `det(v,z) ≡ s' + t (mod L)` for some `0 <= t < H`.
Adding an element of `Lambda` with `det = L m` puts it in `Sigma`. Injectivity: two lifts in `Sigma` differ by an
element of `Lambda` with `det` in `L Z ∩ (-H, H) = {0}`, hence by an element of `Z w`.
For `T_I` the same argument applies, since `det(v, a w + b H u) = b H`, so `det(v, Lambda_H) = H Z` and
`Lambda_H ∩ Z v = Z w`.

(b) Translations of `T_I` commute.

(c) Let `z in Sigma` lift `x`. If `z + e1 in Sigma`, then `nb(x) = pi(z + e1) = x + e1`. Otherwise
`z + e1 -+ H u in Sigma` represents `phi(x) + e1`, and it projects to `x + e1 -+ H u`. This differs from
`x + e1` in `G`, because the rows differ by `H mod L`, which is not 0.
- `z + e1` leaves `Sigma` exactly when `det(v,z) - v2` does. Since `H >= |v2|`, this happens on exactly
  `|v2|` height levels: the bottom ones if `v2 > 0`, the top ones if `v2 < 0`.
- Each height level of `Sigma/Zw` is a coset of `Z v` modulo `Z w`, which has `k` points.
- The same count with `+v1` gives `R_c`.

(d) The levels found in (c) are within `max(|v1|,|v2|) = l` of the bottom or the top. QED.

**The reglued cover.** Suppose the pieces `I_1, ..., I_p` partition `Z/L`, and define `nb, nc` on each
`P_(I_j)` by Lemma 2. Put `b1(x,a) = (nb x, a + beta(x))` and `c1(x,a) = (nc x, a + gamma(x))`. Then:
- `b1 c1 (x,a) = (nb nc x, a + gamma(x) + beta(nc x))` and `c1 b1 (x,a) = (nc nb x, a + beta(x) + gamma(nb x))`.
  So `(b1, c1)` commutes iff the charge
  `kappa1(x) = beta(x) + gamma(nb x) - gamma(x) - beta(nc x)` vanishes.
- `kappa1(x)` depends only on `x`, `nb x` and `nc x`. So `kappa1(x) = kappa(x)` unless `x in R_b ∪ R_c`.
- *(Stokes)* `nb` and `nc` permute each `P_(I_j)`, so `sum over P_(I_j)` of `kappa1` is `0`.
- *(Moves)* Changing `beta(y)` by `delta` changes `kappa1` only at `y` (by `+delta`) and at `nc^-1 y`
  (by `-delta`). Changing `gamma(y)` changes it only at `nb^-1 y` and `y`.
  - Under `phi` these are the edges `phi(y) -- phi(y) - e2` and `phi(y) -- phi(y) - e1` of the square
    grid graph of `T_I`.
  - Each grid edge belongs to exactly one site.
  - So Lemma 6 of the torus note holds on `T_I` verbatim, for any tree subgraph `Y` of the grid graph whose
    vertex set contains the charged vertices: `kappa1` can be cleared on `T_I` with `|E(Y)|` site changes.
  - The proof pushes leaf charges to their parents; uncharged vertices of `Y` are harmless.

## 3. The band

**Lemma 3.** Assume `H >= |v|_1` and let `sigma` be an integer. Then the image `B_sigma` in `T_I` of
`{z : sigma <= det(v,z) < sigma + |v|_1}` has exactly `lambda_1` points and is connected in the grid graph.

*Proof.* The window has length `|v|_1 <= H`, so as in Lemma 2(a) its image is a bijective copy of
`|v|_1` levels, each of `k` points. That gives `k |v|_1 = lambda_1` points.

*Connectivity.*
- If `v1 v2 = 0`, then `|v|_1 = 1`. The band is one level `x + Z v` with `v = +-e_i`, which is a grid cycle.
- Otherwise put `f1 = sgn(v2) e1` and `f2 = sgn(v1) e2`, so that `det(v,f1) = -|v2|` and `det(v,f2) = |v1|`.
- For `z` in the window, let the successor be `z + f1` if `det(v,z) - |v2| >= sigma`, and `z + f2`
  otherwise. In the second case `det(v,z) < sigma + |v2|`, so `det(v, z + f2) < sigma + |v|_1`. Either way the
  successor stays in the window.
- On relative heights modulo `|v|_1`, the successor is the rotation by `-|v2|`. Since
  `gcd(|v2|, |v|_1) = gcd(v1, v2) = 1`, `|v|_1` steps visit every level once. The walk then returns to
  its level, displaced by `+-v`, because it took `|v1|` steps `f1` and `|v2|` steps `f2`.
- Continuing for `k` rounds visits the `k` points `z + j v` of each level modulo `Z w`. So the walk
  covers the whole band. QED.

**Lemma 4 (seam zone).** Assume `H >= 2l`, and let `sigma = s' - l`. Every `x in P_I` whose relative height
lies in `[0, l) ∪ [H - l, H)` has `phi(x)` in `B_sigma` or one grid step away from it.

*Proof.*
- Modulo `H`, the relative height `t'` of `x` lies in `[-l, l)`, because `H >= 2l`. If `t' < -l + |v|_1`,
  then `phi(x)` is in `B_sigma`.
- Otherwise `-l + |v|_1 <= t' < l`. Let `f` be the unit step with `det(v,f) = -l`: `f = -sgn(v1) e2` if
  `l = |v1|`, and `f = sgn(v2) e1` if `l = |v2|`.
- Then `phi(x) + f` has relative height `t' - l` in `[-2l + |v|_1, 0)`. This is contained in
  `[-l, -l + |v|_1)`, since `|v|_1 >= l`. QED.

## 4. Proof of the theorem

Let `kappa = a delta_(x_0) - a delta_(x_0+g)`.

**If `|g|_1 <= lambda_1`**, use Theorem A of the torus note: `dist <= |A| |g|_1 <= 4 rho`.

**Otherwise** `m_0 = lambda_1`, and the lower bound gives `rho >= |A| ceil(lambda_1/2)/2 >= |A| lambda_1/4`.

Let `r_0 = r(x_0)`, `r_1 = r(x_0 + g)`, and let `D <= L/2` be their cyclic distance in `Z/L`. Exchanging the two
charges (and replacing `a` by `-a`) if necessary, we may assume `r_1 - r_0 ≡ D (mod L)`.

*Case `D <= 2l` (path cut).*
- The lifts of `g` have `det(v, .)` in `D + L Z`, so some lift `z` has `det(v,z) = D`.
- By Lemma 1 and `D <= 2l <= 2|v|_2`, `|w|_2 <= lambda_1`, and `lambda_1 >= 1`:
  `|g|_1 <= sqrt2 |z + m w|_2 <= sqrt2 (2 + lambda_1/2) <= (5/sqrt2) lambda_1 < 3.54 lambda_1`.
- Transport the charge along a lattice path of length `|g|_1`, which is Lemma 6 of the torus note with a
  single edge. This gives `dist <= |A| |g|_1 < 3.54 |A| lambda_1 < 14.2 rho`.

*Case `D >= 2l + 1` (strip cut).* Then `L >= 2D >= 4l + 2`. The pieces are:
- `I_1 = {r_0, ..., r_1}`, of height `H_1 = D + 1`, with `2l + 2 <= H_1 < L`;
- `I_2 = {r_1 + 1, ..., r_0 - 1}`, of height `H_2 = L - D - 1 >= D - 1 >= 2l`.

Build `(b1, c1)` as in Section 2.
- By Lemma 2(c), `|R_b| + |R_c| = 2 lambda_1` over both pieces, and `b1, c1` differ from `b, c` exactly at these sites.
- The charged set `Q = supp kappa1` lies in `R_b ∪ R_c ∪ {x_0, x_0 + g}`. So `|Q| <= 2 lambda_1 + 2`.
- For `I_1`, take `s' = det(v, z_0)` for a lift `z_0` of `x_0`. Then `x_0` has relative
  height `0` and `x_0 + g` has relative height `D = H_1 - 1` in `I_1`.
- By Lemma 2(d), every point of `Q` has relative height in `[0,l) ∪ [H-l, H)` in its piece.

In each piece `I_j`, let `V_j = B_sigma ∪ (Q ∩ P_(I_j))`, with `sigma = s'_j - l`.
- By Lemmas 3 and 4 (`H_j >= 2l >= |v|_1`), the grid subgraph on `V_j` is connected.
- A spanning tree `Y_j` has `|V_j| - 1 <= lambda_1 - 1 + |Q ∩ P_(I_j)|` edges.
- The total charge on `T_(I_j)` is 0 (Stokes). Tree cancellation clears `kappa1` on `T_(I_j)` with
  `|E(Y_j)|` fibre changes, leaving the base maps `nb, nc` alone.

Summing over the two pieces, there are at most `2(lambda_1 - 1) + 2 lambda_1 + 2 = 4 lambda_1` fibre changes.

The resulting pair `(b'', c'')` commutes. It differs from `(b, c)` on the fibres over at most
`2 lambda_1 + 4 lambda_1 = 6 lambda_1` sites. Hence `dist <= 6 |A| lambda_1 <= 24 rho`.

Across the cases, `dist <= max(4, 14.2, 24) rho = 24 rho`. QED.

## 5. Remarks

- **Where the one-sided method lost.** The torus note keeps the word `B = b^v1 c^v2` and back-substitutes
  `b'' = B^u2 C''^-v2`. That loses a factor `|u|,|v| <= lambda_1` twice, and a Stokes error on staircase
  words. Here `b` and `c` are changed directly, at `6 lambda_1` sites near the two cut lines and along
  two digital lines.
- **Sharpness.** The constant is not sharp. Exhaustively for `N <= 16`, the best of the path cut and all
  two-cut strips has `dist/rho <= 1.667` (`strips.py`, 2233 cases). The explicit construction above,
  checked assertion by assertion by `strips_band.py`, changes at most `3.34 lambda_1` sites and has
  `dist/rho <= 4.5` on 4342 exhaustive cases (`N <= 20`, `strips-summary.txt`).
- **Several charges.** With `n` charges, cutting the row circle at every charged row gives pieces of
  height `>= 2l` after merging close rows. This suggests `O(|A|(n lambda_1 + n^2))` for the thin
  case of Theorem B. It is not proved here, because merged clusters are not neutral in general.
- **Non-abelian fibre.** In each piece the new charges are elements of the fibre group, defined only up to conjugacy. Cancelling them
  along the band needs the ordered product around the band to be trivial, not just the sum. This is where
  a non-abelian version must do more work, consistent with
  `centralizer-rounding-cannot-bound-rank-distance-by-profile`.
