---
rg: 2
id: hermitian-edge-trace-norm-web-rank-k5-n22-n29-sharper-cover
kind: route
title: Certify c(K_5 plus a pendant, w) >= 6.2829 with the weighted branch-and-bound and cover C_22^5 and C_29^5 by rotations of {0,1,2,3,4,9}
target: hermitian-edge-trace-norm-web-rank-k5-n22-n29
requires:
  - hermitian-edge-trace-norm-web-rank-k5-weighted-pendant
artifacts:
  - research/hermitian-edge-trace-norm-web-rank-k4-n13-n14-weighted-cover.md
  - research/hermitian-edge-trace-norm-web-rank-k5-weighted-pendant-cover.md
  - experiments/hermitian-edge-trace-norm-web-k4-weighted-2026-09-19/fastbbw.py
  - experiments/hermitian-edge-trace-norm-web-k4-weighted-2026-09-19/runw.sh
  - experiments/hermitian-edge-trace-norm-web-k5-weighted-2026-09-19/k5p_62829.log
---

A computer-assisted proof. It is unreviewed and not Lean-verified. Lane w11-078, 2026-09-19.

Notation: `H`, `w = (3/4, 3/4, 3/4, 3/4, 1, 1/5)`, `|w| = 21/5` and `c(H, w)` are as in
`hermitian-edge-trace-norm-web-rank-k4-n13-n14-weighted-cover`.

## Step 1. `c(H, w) >= 6.2829`

This is the certificate of Step 3 of `hermitian-edge-trace-norm-web-rank-k4-n13-n14-weighted-cover`:
the same program, graph, weights, root, first phase and symmetry conditions, at a higher target.
Only the per-edge modulus thresholds `T_e`, which the program derives from the target, change; they
are printed on the first line of the log. The soundness and symmetry arguments of that route do not
depend on the target.

The command, in `experiments/hermitian-edge-trace-norm-web-k4-weighted-2026-09-19/`, is

```text
SYM='0.1<0.2,0.3,1.2,1.3,2.3;0.2<0.3,1.2,1.3' ROOT=4 FIRST=0-1 CKEVERY=200 \
  bash runw.sh k5p_62829 'W14/1.2.3.4:0,1,2,3,4,8' 6.2829 3/4,3/4,3/4,3/4,1,1/5 0 1.5707963267948966
```

The final line of `k5p_62829.log` reads `ALL CLOSED`. The graph string `W14/...:0,1,2,3,4,8` only
names `H`.

## Step 2. Covering

By Step 2 of `hermitian-edge-trace-norm-web-rank-k5-weighted-pendant-cover`, for `n >= 15` every
admissible `C` on `C_n^5` has `||C||_1 >= n c(H, w)/|w|`. The rotations of `{0, 1, 2, 3, 4, 9}`
are the windows.

## Step 3. Arithmetic, exact in rationals

- `n = 22`: `(22 x 6.2829 x 5/21)^2 = 1083.0963... >= 1083 = (19 sqrt3)^2`.
- `n = 29`: `(29 x 6.2829 x 5/21)^2 = 1881.9917... >= 1875 = (25 sqrt3)^2`.

So `||C||_1 >= 19 sqrt3` on `C_22^5` and `||C||_1 >= 25 sqrt3` on `C_29^5`.
