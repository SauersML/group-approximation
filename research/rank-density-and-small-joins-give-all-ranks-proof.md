---
rg: 2
id: rank-density-and-small-joins-give-all-ranks-proof
kind: route
title: The supremum of the directed set L'_f has rank exactly f once rank density supplies approximants way below f
target: rank-density-and-small-joins-give-all-ranks
requires: []
---

Notation as in the target.

**Standard inputs.**
- *(C1)* For separable `A`, `Cu(A)` is countably based. Every upward directed
  subset of a countably based Cu-semigroup has a supremum. Thiel,
  arXiv:1711.04721, `prp:ctblBasedDCPO`, as invoked in the sentence before
  `dfn:alpha`. Every element is the supremum of the elements way below it.
- *(C2)* Each `d_tau` is additive, order preserving and preserves suprema of
  increasing sequences. `QT(A)` is a compact metrizable Choquet simplex, and
  every `f in LAff(K)` is the pointwise supremum of an increasing sequence in
  `Aff(K)` (Edwards; see `all-ranks-occur-iff-continuous-ranks-are-dense-proof`).
- *(C3) A way-below test in `LAff(K)`.* If `f' <= h` with `h in Aff(K)`,
  `eps > 0` and `h + eps <= f`, then `f' << f`.
  - Let `f_k` increase with supremum at least `f`.
  - The open sets `{f_k > h + eps/2}` increase and cover the compact `K`, so
    some `f_k > h + eps/2 >= f'`.

**Step 1: `L'_f` is downward closed.** If `b <= a' << a` with `d(a) << f`,
then `b << a`, so `b in L'_f`.

**Step 2: `alpha(f)` exists and `d(alpha(f)) <= f`.**
- `0 in L'_f`, and (SJ) makes `L'_f` upward directed, so `alpha(f) = sup L'_f`
  exists by (C1).
- Fix a countable basis `B`. Every `a' in L'_f` is the supremum of basis
  elements way below it, and these lie in `L'_f` by Step 1. So
  `alpha(f) = sup (B cap L'_f)`.
- `B cap L'_f` is countable and directed, so it has a cofinal increasing
  sequence `(a_k)` with `alpha(f) = sup_k a_k`.
- Each `a_k` satisfies `d(a_k) <= d(a) <= f` for some witness `a`. By (C2),
  `d(alpha(f)) = sup_k d(a_k) <= f`.

**Step 3: `d(alpha(f)) >= f`.**
- By (C2) choose `g_n in Aff(K)` increasing with supremum `f`, and put
  `m = min f > 0`.
- As in `all-ranks-occur-iff-continuous-ranks-are-dense-proof`, discard finitely
  many `n` so that `min g_n > m/2`. Put `eps_n = m 2^(-n-2)`, so `g_n - eps_n`
  is strictly positive.
- (RD) gives `a_n` with `|d(a_n) - (g_n - 3 eps_n/4)| < eps_n/4`, so
  `g_n - eps_n <= d(a_n) <= g_n - eps_n/2`.
- By (C3) with `h = g_n - eps_n/2` and `h + eps_n/2 = g_n <= f`, we get
  `d(a_n) << f`.
- Every `a'' << a_n` lies in `L'_f`, witnessed by `a = a_n`, so `a'' <= alpha(f)`.
  Since `a_n = sup {a'' : a'' << a_n}`, we get `a_n <= alpha(f)`.
- Hence `d(alpha(f)) >= d(a_n) >= g_n - eps_n`, whose supremum over `n` is `f`.

Steps 2 and 3 give `d(alpha(f)) = f`. A positive representative of
`alpha(f)` realizes `f`.

**Corollary: strict comparison and (RD) give (SJ).** Let `a' << a` and
`b' << b` with `d(a), d(b) << f`.
1. `LAff(K)` is a countably based domain (Thiel, `prp:llInLAff`), so the
   elements way below `f` form a directed set. There is `f' in LAff(K)` with
   `d(a), d(b) <= f' << f`. The same proposition gives `h in Aff(K)` and
   `eps > 0` with `f' <= h` and `h + eps <= f`. Thiel uses exactly these two
   steps in his directedness lemma for `L'_f`.
2. (RD) gives `c_0 in M_infinity(A)_+` with `|d(c_0) - (h + eps/2)| < eps/8`.
   So `h + 3eps/8 < d(c_0) < h + 5eps/8`, and `d(c_0) << f` by (C3).
3. The sets `{d((c_0 - 1/k)_+) > h + eps/4}` are open, increase and cover `K`.
   So some `c' = [(c_0 - 1/k)_+]` satisfies `d(c') > h + eps/4`, and
   `c' << [c_0]`.
4. Since `a' << a`, some finite-matrix element `a_1` has
   `a' <= [a_1] <= a`. Then `d(a_1) <= h < d(c')`, so strict comparison gives
   `a' <= [a_1] <= c'`. Likewise `b' <= c'`.
5. So `c' in L'_f`, witnessed by `c = [c_0]`, is an upper bound for `a'` and `b'`,
   and `L'_f` is upward directed. Square.
