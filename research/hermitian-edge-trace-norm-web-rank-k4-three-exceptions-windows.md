---
rg: 2
id: hermitian-edge-trace-norm-web-rank-k4-three-exceptions-windows
kind: route
title: Cover C_n^4 by five-vertex clique windows and certify c(K_5) >= 7.2169 by a symmetry-reduced exact-rational SDP branch-and-bound
target: hermitian-edge-trace-norm-web-rank-k4-three-exceptions
requires: []
artifacts:
  - research/hermitian-edge-trace-norm-odd-antihole-facets-by-size.md
  - research/hermitian-edge-trace-norm-web-rank-large-k-clique-windows.md
  - research/hermitian-edge-trace-norm-web-rank-k4-six-exceptions-windows.md
  - experiments/hermitian-edge-trace-norm-webs-robust-2026-09-18/graphbb_r.py
  - experiments/hermitian-edge-trace-norm-web-k4-2026-09-18/README.md
  - experiments/hermitian-edge-trace-norm-web-k4-2026-09-18/fastbb.py
  - experiments/hermitian-edge-trace-norm-web-k4-2026-09-18/run.sh
  - experiments/hermitian-edge-trace-norm-web-k4-2026-09-18/k5a.log
  - experiments/hermitian-edge-trace-norm-web-k4-2026-09-18/k5b.log
  - experiments/hermitian-edge-trace-norm-web-k4-2026-09-18/control_7.24.log
  - experiments/hermitian-edge-trace-norm-web-k4-2026-09-18/symtest.py
  - experiments/hermitian-edge-trace-norm-web-k4-2026-09-18/symtest.log
  - experiments/hermitian-edge-trace-norm-web-clique-lp-2026-09-18/web_clique_lists.py
  - experiments/hermitian-edge-trace-norm-web-k4-2026-09-18/web_clique_lists_k4.log
---

A computer-assisted proof. It is unreviewed and not Lean-verified. Lane w9-078, 2026-09-18.

Notation: `c(F)` is the minimum of `||C||_1` over admissible `C` on `F`, and `c_5 = c(K_5)`.

## Step 1. Windows

This is Step 1 of `hermitian-edge-trace-norm-web-rank-k4-six-exceptions-windows`.

- The `n` sets `{t, ..., t+4}` (mod `n`) are cliques `K_5` of `C_n^4`, and each vertex lies in 5 of them.
- The covering lemma (Lemma 1 of `hermitian-edge-trace-norm-odd-antihole-facets-by-size`) gives
  `||C||_1 >= (n/5) c_5`.
- So `(R_{n,4})` holds whenever `n L/5 >= sqrt3 (n - floor(n/5))` for some `0 < L <= c_5`.

## Step 2. `c_5 >= 7.2169`

`run.sh k5a K5 7.2169 1.877 0 0.7853981633974483` and `run.sh k5b K5 7.2169 1.877 0.7853981633974483 1.5707963267948966`
were run with `SYM` set to `SYM_K5` of the experiment README. Each runs `fastbb.py` on `K_5`.

- The BFS tree from vertex `0` is the star `01, 02, 03, 04`.
- The six free phases are those of `12, 13, 14, 23, 24, 34`, in that order.

A box is closed by the certificate of `graphbb.py` / `graphbb_r.py`, unchanged:

- Gauge the star entries real and positive.
- On a phase box with all moduli in `[1, T]`, take a Gaussian-rational Hermitian `Z` with `I - Z` and
  `I + Z` positive definite, checked by exact Fraction pivots. Then `||K||_1 >= tr(ZK)`.
- Minimise `tr(ZK)` edge by edge over the moduli and the phase arc, with exact cosine ranges and
  outward rounding.
- The box is closed when that bound is at least the double `7.2169`.

Two further reductions are proved in the experiment README.

1. **Pinching cut.** If some `|K_ij| = t > T`, pinch into the blocks `{i, j}` and the remaining
   triangle `R`. This gives `||K||_1 >= 2t + ||K_R||_1 > 2T + 2 sqrt3`. The bound
   `||K_R||_1 >= 2 sqrt3` holds for every `3 x 3` zero-diagonal Hermitian matrix with entries of
   modulus at least `1`, because `sum lambda^2 >= 6` and `sum lambda^2 <= s^2/2`. With `T = 1.877`,
   `2T + 2 sqrt3 (1 - 1e-12) = 7.2181 >= 7.2169`. The script asserts this.
2. **Fundamental domain.** `S_5`, `conj` and `-K` preserve the trace norm and admissibility.
   Modulo gauge, they permute the ten values `u(phi(T)) = dist(phi(T), pi Z)`, where `phi(T)` is the
   phase of triangle `T`. So every admissible `K` has an image with:
   - `th_12 in [0, pi/2]`;
   - `u(phi(012))` least among all ten triangles;
   - `u(phi(013))` least among the six triangles `{a, b, x}` with `{a, b}` in `{0, 1, 2}` and `x` in `{3, 4}`.

   The orbit argument is in the README. A box on which one of these inequalities fails strictly
   everywhere (by exact interval arithmetic on signed phase sums) is dropped. `symtest.py` checks
   the claim independently on 3000 random `K` (`symtest.log`).

Results:

- `k5a.log` (`th_12 in [0, pi/4]`) ends with `ALL CLOSED`: 5665 closed boxes and 549 symmetry drops.
- `k5b.log` (`[pi/4, pi/2]`) ends with `ALL CLOSED`: 3966 closed boxes and 1424 symmetry drops.
- Together they took 20027 solves.

Every other change in `fastbb.py` only chooses the candidate `Z` or the split, as the README
explains. `control_7.24.log`, the same run at target `7.24 > 5 + sqrt5`, stops with `FAIL` at an
admissible point with `||C||_1 = 7.23957`.

## Step 3. Arithmetic

Let `b = 8125507037692533/2^50`, the exact double `7.2169`. `web_clique_lists.py 5:b` checks Step 1
with `L = b` exactly.

- Take `s = 17320509/10^7 > sqrt3` and `eps = b - 4 s = 0.28870 > 0`.
- The inequality is equivalent to `n (b - 4 sqrt3) >= sqrt3 (n mod 5)`, so it holds for all
  `n >= floor(4 s/eps) + 2 = 25`.
- For `10 <= n < 25` the script checks it exactly.

`web_clique_lists_k4.log` gives the failures:

```text
k=4 m=5 L_m=7.216900 eps_m>=0.28870 all n>=25 pass; exceptions n>=2k+2: [13, 14, 19]
```

So every other `n >= 10` satisfies `(R_{n,4})`. ∎
