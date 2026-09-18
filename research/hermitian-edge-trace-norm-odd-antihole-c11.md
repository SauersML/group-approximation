---
rg: 2
id: hermitian-edge-trace-norm-odd-antihole-c11
kind: claim
title: Admissible matrices on the complement of the 11-cycle have trace norm at least 9 sqrt3
artifacts:
  - experiments/hermitian-edge-trace-norm-antihole-2026-09-18/README.md
  - experiments/hermitian-edge-trace-norm-antihole-2026-09-18/graphbb.py
  - experiments/hermitian-edge-trace-norm-antihole-2026-09-18/k5hilane.sh
  - experiments/hermitian-edge-trace-norm-antihole-2026-09-18/k5hi_n16_s7.log
distinct_from:
  hermitian-edge-trace-norm-odd-antihole-facets: that is every odd antihole; this is the single case n = 11, the only one it leaves open.
  hermitian-edge-trace-norm-clique-inequality-k5: that is c_5 >= 4 sqrt3 = 6.928; the route proposed here needs the stronger c_5 >= 45 sqrt3/11 = 7.0857 (numerical c_5 = 5 + sqrt5 = 7.236).
---

**OPEN - reduced to a finite computation.** Let `H = C̄_11` (vertices `Z_11`, `i ~ j` iff
`i - j` is not in `{0, 1, -1}` mod 11). Every admissible `C` on `H` should satisfy

```text
|| C ||_1  >=  9 sqrt3  =  15.5885 .
```

**Sufficient condition (proved).** `C̄_11` has the 11 maximum cliques
`U_t = {t, t+2, t+4, t+6, t+8}`, and each vertex lies in exactly 5 of them. Write `C = P - N` with
`P, N >= 0` and `|C| = P + N`. Then for every vertex set `U`,
`||C_U||_1 <= tr P_U + tr N_U = sum_{i in U} |C|_ii`. Summing over the `U_t` gives

```text
|| C ||_1  >=  (1/5) sum_t || C_{U_t} ||_1  >=  (11/5) c_5 ,
```

where `c_5` is the minimum trace norm over admissible `C` on `K_5`. So `c_5 >= 45 sqrt3 / 11 =
7.08566` suffices. The numerical value is `c_5 = 5 + sqrt5 = 7.2361`, a margin of 2.1%.

**The computation.** `graphbb.py K5 7.0857 3.55 3 lo hi` runs the `K_5` scheme of
`hermitian-edge-trace-norm-clique-inequality-k5` with `TARGET = 7.0857` and `T = 3.55`. The same
symmetry reduction applies: 16 slices of `theta_23 in [0, pi/2]`. The driver is `k5hilane.sh 16 <i> ...`.
Finishing all 16 slices also proves the `K_5` claim, since `7.0857 > 6.9282`.

## Attempts

- 2026-09-18 (w7-078): **the kernel LP of the by-size route falls short.** At degree 5 on the
  `Z_11 x disc` Delsarte LP it gives `15.53`, which is `0.9962` of the target (the same LP
  proves `n = 13`). Degree 6 gives the same `0.9962`, so raising the degree does not help. Uniform-matching
  averaging of the rank-one bound gives about `0.93`.
- 2026-09-18 (w7-078): **the `K_5` branch-and-bound at `7.0857` is running; 1 of 16 slices is closed.**
  Slice 7 (`theta_23 in [0.6872, 0.7854]`) prints `ALL CLOSED`: 59042 boxes, 83292 solves, 2765 s,
  smallest centre value `7.255450` (`k5hi_n16_s7.log`). That is about twice the boxes of the same slice at
  `6.928`. Expect about 45 CPU-minutes per slice, or roughly 12 CPU-hours for all 16. Slices 0-3 are running.
