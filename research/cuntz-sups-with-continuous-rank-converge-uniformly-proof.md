---
rg: 2
id: cuntz-sups-with-continuous-rank-converge-uniformly-proof
kind: route
title: Dini's theorem on continuous traces of cut-downs, plus compact containment, gives uniform convergence of Cuntz approximants
target: cuntz-sups-with-continuous-rank-converge-uniformly
requires: []
---

Standard inputs.
- (R) Rørdam's lemma in the form: if `||x - y|| < eps` and `t >= 0`, then
  `(x - eps - t)_+ <~ (y - t)_+`. (Apply the usual form `||x - y'|| < eps'`
  implies `(x - eps')_+ <~ y'` to `y' = (y - t)_+`, `||y - y'|| <= t`.)
- (Q) Every `tau in QT(A)` is monotone on positive elements, and
  `d_tau(x) = lim_(eps -> 0) tau(f_eps(x))` for continuous `0 <= f_eps <= 1`
  increasing to the indicator of `(0, infinity)`. `d_tau` is order preserving on
  `Cu(A)` and preserves suprema of increasing sequences, and
  `[x] = sup_eps [(x - eps)_+]`.
- (T) For `b in M_k(A)_+` and continuous `g` with `g(0) = 0`, the map
  `tau -> tau(g(b))` is continuous on `QT(A)` (definition of the topology).
- (W) `[(x - eps)_+] << [x]` in `Cu(A)`, and if `z << sup_n x_n` for an
  increasing sequence then `z <= x_n` for all large `n`.

Put `h_d(t) = min(1, max(0, (t - d)/d))` for `d > 0`.

**Step 1: continuous squeeze.** The compressions of `a` by the units of `K` lie
in `M_k(A)_+` and converge to `a` in norm. Choose `b_j in M_(k_j)(A)_+` with
`||a - b_j|| < 1/j`, and put `c_j = (b_j - 1/j)_+` and
`g_j(tau) = tau(h_(1/j)(c_j))`. By (T), `g_j` is continuous.

- *Upper bound.* `h_(1/j)(t) = g((t - 1/j)_+)` with `g(s) = min(1, j s)`, so
  `h_(1/j)(c_j) = g(x)` for `x = (c_j - 1/j)_+`. Since `0 <= g <= 1` and `g(0) = 0`,
  the continuous functions `min(g, f_eps)` increase to `g` uniformly on the
  spectrum of `x` (Dini), so by (Q) and norm continuity of bounded quasitraces on
  positive elements, `tau(g(x)) <= lim_eps tau(f_eps(x)) = d_tau(x)`. Hence
  `g_j(tau) <= d_tau((c_j - 1/j)_+) = d_tau((b_j - 2/j)_+) <= d_tau((a - 1/j)_+)`,
  the last step by (R) with `eps = 1/j`, `t = 1/j`, `x = b_j`, `y = a`.
- *Lower bound.* `h_(1/j)(t) = 1` for `t >= 2/j`, so
  `f_eps((t - 2/j)_+) <= h_(1/j)(t)` for all `eps`. By (Q),
  `g_j(tau) >= d_tau((c_j - 2/j)_+) = d_tau((b_j - 3/j)_+) >= d_tau((a - 4/j)_+)`,
  the last step by (R) with `eps = 1/j`, `t = 3/j`, `x = a`, `y = b_j`.

So `d((a - 4/j)_+) <= g_j <= d((a - 1/j)_+) <= d(a)`.

**Step 2: Dini.** Put `G_j = max(g_1, ..., g_j)`. It is continuous, increasing
in `j`, and `d((a - 4/j)_+) <= G_j <= d((a - 1/j)_+)` because
`d((a - 1/i)_+) <= d((a - 1/j)_+)` for `i <= j`. By (Q) the lower bound
increases pointwise to `d(a)`, so `G_j -> d(a)` pointwise. `QT(A)` is compact and
`d(a)` is continuous and finite, so by Dini's theorem `G_j -> d(a)` uniformly.

**Step 3: compact containment.** Fix `j`. By (W), `[(a - 1/j)_+] << [a] = sup_n [a_n]`,
so there is `n_j` with `[(a - 1/j)_+] <= [a_n]` for `n >= n_j`. Then
`G_j <= d((a - 1/j)_+) <= d(a_n) <= d(a)` for `n >= n_j`. Given `eps`, choose
`j` with `d(a) - G_j < eps` everywhere; then `n_0 = n_j` works. Square.

**The branch-trace corollary.** Step 1 of
`doubling-ah-finite-stage-continuous-ranks-constant-proof` gives, for `b` at
stage `<= M` and `y in X_M`, `d_(sigma_y)(b) = beta_M rank b(y)/r_M + c_(b,M)` with
`c_(b,M)` independent of `y`. Apply the Theorem with `tau = sigma_y`.
