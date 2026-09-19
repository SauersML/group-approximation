---
rg: 2
id: hermitian-edge-trace-norm-web-rank-k4-six-exceptions-windows
kind: route
title: Cover C_n^4 by five-vertex clique windows and certify c(K_5) >= 7.168 by a robust exact-rational SDP branch-and-bound
target: hermitian-edge-trace-norm-web-rank-k4-six-exceptions
requires: []
artifacts:
  - research/hermitian-edge-trace-norm-odd-antihole-facets-by-size.md
  - research/hermitian-edge-trace-norm-clique-inequality-k4-proof.md
  - research/hermitian-edge-trace-norm-web-rank-large-k-clique-windows.md
  - experiments/hermitian-edge-trace-norm-webs-2026-09-18/graphbb.py
  - experiments/hermitian-edge-trace-norm-webs-robust-2026-09-18/README.md
  - experiments/hermitian-edge-trace-norm-webs-robust-2026-09-18/graphbb_r.py
  - experiments/hermitian-edge-trace-norm-webs-robust-2026-09-18/lane.sh
  - experiments/hermitian-edge-trace-norm-webs-robust-2026-09-18/k5_a.log
  - experiments/hermitian-edge-trace-norm-webs-robust-2026-09-18/k5_b.log
  - experiments/hermitian-edge-trace-norm-web-clique-lp-2026-09-18/web_clique_lists.py
  - experiments/hermitian-edge-trace-norm-web-clique-lp-2026-09-18/web_clique_lists_k4.log
---

A computer-assisted proof. It is unreviewed and not Lean-verified. Lane w8-078, 2026-09-18.

Notation: `c(F)` is the minimum of `||C||_1` over admissible `C` on `F`, and `c_5 = c(K_5)`.

## Step 1. Windows

This is Step 1 of `hermitian-edge-trace-norm-web-rank-large-k-clique-windows` with `m = 5`. The `n`
sets `{t, ..., t+4}` (mod `n`) are cliques `K_5` of `C_n^4`, and each vertex lies in 5 of them. The
covering lemma (Lemma 1 of `hermitian-edge-trace-norm-odd-antihole-facets-by-size`) gives
`||C||_1 >= (n/5) c_5`. So `(R_{n,4})` holds whenever `(n L/5)^2 >= 3 (n - floor(n/5))^2` for some
`0 < L <= c_5`.

## Step 2. `c_5 >= 7.168`

`lane.sh K5 7.168 3.6 3 TAG A_LO A_HI` runs `graphbb_r.py K5 7.168 3.6 3 A_LO A_HI` on the complete
graph `K_5`. The BFS tree from vertex `0` is the star `01, 02, 03, 04`. The six free phases are
those of `12, 13, 14, 23, 24, 34`, in that order. The certificate is that of `graphbb.py`
(`experiments/hermitian-edge-trace-norm-webs-2026-09-18/`), which is
`hermitian-edge-trace-norm-clique-inequality-k4-proof` Steps 1-4 for general `m`:

- Gauge the star entries real and positive. If some `|K_ij| > T = 3.6`, then
  `||K||_1 >= 2 |K_ij| > 7.2 >= 7.168`.
- Otherwise, for a Gaussian-rational Hermitian `Z` with `I - Z` and `I + Z` positive definite
  (checked by exact Fraction pivots), `||K||_1 >= tr(ZK)`. This is minimised over the moduli in
  `[1, T]` and the phase box edge by edge, with exact cosine ranges and outward rounding.
- A box is closed when that bound is `>= 7.168` (the double, which is `>=` the decimal `7.168`).
  Otherwise it is bisected.

`graphbb_r.py` differs from `graphbb.py` only in how the candidate `Z` is found: one SDP over the
whole phase box instead of the dual optimum at its centre. The candidate is rounded and checked
exactly as before (see the experiment README). `k5_a.log` (first phase in `[0, pi/4]`) and
`k5_b.log` (`[pi/4, pi/2]`) both end with `ALL CLOSED`, in 23478 boxes and 45264 solves in total.

Why `[0, pi/2]` suffices. `C -> conj(C)` negates every free phase. With `E = diag(1, -1, -1, -1, -1)`,
the map `C -> -E C E` keeps the star entries (`-E_00 E_jj = 1`) and negates every other entry, so
it shifts every free phase by `pi`. Both maps preserve the trace norm, the zero pattern and the
moduli. So the phase `theta` of `12` can be moved to `-theta`, `theta + pi` and `pi - theta`, and one
of these lies in `[0, pi/2]`.

## Step 3. Arithmetic

Let `b = 8070450532247929/2^50`, the exact double `7.168`. `web_clique_lists.py 5:b` checks Step 1
with `L = b` exactly. With `s = 17320509/10^7 > sqrt3` and `eps = b - 4 s = 0.23980 > 0`, the
inequality holds for all `n >= floor(4 s/eps) + 2 = 30`, since it is equivalent to
`n (b - 4 sqrt3) >= sqrt3 (n mod 5)`. For `10 <= n < 30` the script checks it exactly.
`web_clique_lists_k4.log` gives the failures:

```text
k=4 m=5 L_m=7.168000 eps_m>=0.23980 all n>=30 pass; exceptions n>=2k+2: [12, 13, 14, 18, 19, 24]
```

Every other `n >= 10` satisfies `(R_{n,4})`. ∎
