# Units on the radius-four census supports with any inverse support (2026-09-13)

Claims: `research/promislow-radius4-orbit1-units-need-zeta8-any-inverse.md` and
`research/promislow-radius4-orbit0-units-need-zeta8-any-inverse.md`.
Routes: `research/promislow-radius4-orbit1-units-need-zeta8-any-inverse-proof.md` and
`research/promislow-radius4-orbit0-units-need-zeta8-any-inverse-proof.md`.

All runs used Sage 10.7 (`sage -python`) on MSI, partition `agsmall`, in
`/scratch.global/sauer354/uc0/t00103/anc`. That is the directory of
`promislow-radius4-support-pairs-zeta8-2026-09-12.md`, and it holds the same
`census_pairs.json`.

| script (name on MSI) | md5 | slurm jobs |
| --- | --- | --- |
| `promislow-radius4-census-box.py` (`sbox.py`) | `75e59ad624a818ea738f76aa7223125b` | 597558, 598021 |
| `promislow-radius4-census-box-verify.py` (`sbox_verify.py`) | `7f6ca6a4083b627e9ccb2c7a2b959488` | 599042, 689436 |
| `promislow-radius4-census-box-cases.py` (`sbox2.py`) | `1475fa8724be6a203bd5097b8552202d` | 689435 |

`census_pairs.json` has md5 `88d50831522fe612ef9412f27237bfb3`. Mode `bounds`
writes `sbox_pairs.json` (md5 `1e5080225b5f3600d58ea3a5df69951d`), and the
other two scripts read it. `promislow-radius4-census-box-cases.py` is
`promislow-radius4-census-box.py` with two optional arguments added to mode
`cases`: `only=i,j;...`, which runs only the listed cases, and `from=i`, which
skips rows below `i`. Without them it runs the same computation.

## Representative 1

The support `S_1` of representative 1 of `census_pairs.json`, as
`(s, t)` in the model `(s, t)(s', t') = (ss', t + s t')`, verbatim:

```text
[[[-1, -1, 1], [-3, 0, -1]], [[-1, -1, 1], [-1, -2, -1]], [[-1, -1, 1], [-1, 0, 1]], [[-1, -1, 1], [-1, 2, -1]], [[-1, -1, 1], [1, 0, -1]], [[-1, 1, -1], [-2, -1, 1]], [[-1, 1, -1], [-2, 1, -1]], [[-1, 1, -1], [0, 1, -1]], [[-1, 1, -1], [0, 3, 1]], [[1, -1, -1], [-1, -1, 0]], [[1, -1, -1], [1, -1, 2]], [[1, -1, -1], [1, 1, 2]], [[1, -1, -1], [3, 1, 0]], [[1, 1, 1], [0, 0, -2]], [[1, 1, 1], [0, 0, 0]], [[1, 1, 1], [0, 2, -2]], [[1, 1, 1], [0, 2, 0]], [[1, 1, 1], [2, 0, -2]], [[1, 1, 1], [2, 0, 0]], [[1, 1, 1], [2, 2, -2]], [[1, 1, 1], [2, 2, 0]]]
```

Mode `orbits` of `promislow-radius4-census.py` (job 584612, recorded in the
2026-09-12 artifact) gives this representative an orbit of size 8 and an
inverse support of word radius 5.

## Mode `bounds` (job 597558)

For each representative `S`, the script keeps the elements `g` with
`l_i^m(g) <= max_(h in S) l_i^m(h)` for `i = 0, 1, 2` and `-40 <= m <= 40`.
It starts from the elements whose translation coordinates lie in a range
around the one allowed by `m = 0`, with the parity of `t` fixed by `s`. It
asserts that the elements just outside that range fail the `m = 0` condition,
and the syllable length only grows farther out. `adj(S)`, a support bound from
the adjugate, is printed for comparison and is not used. Verbatim:

```text
orbit 0: |T| = 21, |adj(S)| = 333, |box(S)| = 77 (sizes at m = -40, -1, 0, 1, 40 after intersecting: 339, 105, 77, 77, 77), |both| = 77, T in adj True, T in box True, S^-1 in adj True, S^-1 in box True  [0.1s]
orbit 1: |T| = 21, |adj(S)| = 333, |box(S)| = 77 (sizes at m = -40, -1, 0, 1, 40 after intersecting: 339, 105, 77, 77, 77), |both| = 77, T in adj True, T in box True, S^-1 in adj True, S^-1 in box True  [0.1s]
orbit 2: |T| = 21, |adj(S)| = 333, |box(S)| = 71 (sizes at m = -40, -1, 0, 1, 40 after intersecting: 321, 123, 77, 71, 71), |both| = 71, T in adj True, T in box True, S^-1 in adj True, S^-1 in box True  [0.1s]
orbit 3: |T| = 21, |adj(S)| = 333, |box(S)| = 71 (sizes at m = -40, -1, 0, 1, 40 after intersecting: 321, 123, 77, 71, 71), |both| = 71, T in adj True, T in box True, S^-1 in adj True, S^-1 in box True  [0.2s]
orbit 4: |T| = 21, |adj(S)| = 333, |box(S)| = 71 (sizes at m = -40, -1, 0, 1, 40 after intersecting: 321, 123, 77, 71, 71), |both| = 71, T in adj True, T in box True, S^-1 in adj True, S^-1 in box True  [0.3s]
orbit 5: |T| = 21, |adj(S)| = 333, |box(S)| = 71 (sizes at m = -40, -1, 0, 1, 40 after intersecting: 321, 123, 77, 71, 71), |both| = 71, T in adj True, T in box True, S^-1 in adj True, S^-1 in box True  [0.3s]
orbit 6: |T| = 21, |adj(S)| = 333, |box(S)| = 59 (sizes at m = -40, -1, 0, 1, 40 after intersecting: 285, 111, 63, 59, 59), |both| = 59, T in adj True, T in box True, S^-1 in adj True, S^-1 in box True  [0.4s]
DONE
```

## Mode `cases k box 3600` (job 598021, array `0-6`, 24G)

For representative `k`, the script reads `T' = box(S)` from `sbox_pairs.json`,
asserts `T in T'`, forms the product table of `S` against `T'`, and runs the
case split of the 2026-09-12 route (Step 2) over `Q` with Singular `slimgb`.
It stops any single case after 3600 seconds. It prints a line for every case
whose basis has no nonzero constant, one line after each row `i`, and a
closing line listing the nonempty cases and the timeouts. A timeout decides
nothing.

Slurm record, verbatim:

```text
        598021_0     uc0-sbox    COMPLETED   03:36:22      0:0
        598021_1     uc0-sbox    COMPLETED   02:03:02      0:0
        598021_2     uc0-sbox      TIMEOUT   12:00:10      0:0
        598021_3     uc0-sbox    COMPLETED   05:35:16      0:0
        598021_4     uc0-sbox    COMPLETED   05:01:43      0:0
        598021_5     uc0-sbox    COMPLETED   05:12:29      0:0
        598021_6     uc0-sbox OUT_OF_MEMO+   03:10:08    0:125
```

Representative 1, the whole output with Singular's "no standard basis"
warnings removed:

```text
orbit 1: |S| = 21, |T'| = 77 (box), cells 330  [0.0s]
orbit 1 box case (0,1): GB size 138, dim 1, vdim -1  [136.6s]
orbit 1 box: i = 0 done  [1197.3s]
orbit 1 box: i = 1 done  [1832.7s]
orbit 1 box: i = 2 done  [5676.1s]
orbit 1 box: i = 3 done  [6332.4s]
orbit 1 box: i = 4 done  [6607.5s]
orbit 1 box: i = 5 done  [7044.2s]
orbit 1 box: i = 6 done  [7333.0s]
orbit 1 box: i = 7 done  [7354.0s]
orbit 1 box: i = 8 done  [7356.2s]
orbit 1 box: i = 9 done  [7356.5s]
orbit 1 box: i = 10 done  [7367.3s]
orbit 1 box: i = 11 done  [7368.0s]
orbit 1 box: i = 12 done  [7368.2s]
orbit 1 box: i = 13 done  [7368.3s]
orbit 1 box: i = 14 done  [7368.4s]
orbit 1 box: i = 15 done  [7368.4s]
orbit 1 box: i = 16 done  [7368.5s]
orbit 1 box: i = 17 done  [7368.5s]
orbit 1 box: i = 18 done  [7368.5s]
orbit 1 box: i = 19 done  [7368.5s]
orbit 1 box: i = 20 done  [7368.5s]
orbit 1 box: nonempty cases [(0, 1)]; timeouts []; slowest (1172.0097479820251, (2, 5))  [7368.5s]
DONE
```

Representatives 0 and 2 to 6, every line except the per-row lines, with the
Singular warnings removed, verbatim:

```text
orbit 0: |S| = 21, |T'| = 77 (box), cells 338  [0.0s]
orbit 0 box case (0,1): GB size 138, dim 1, vdim -1  [906.6s]
orbit 0 box case (2,5): TIMEOUT 3600s  [9477.1s]
orbit 0 box: nonempty cases [(0, 1)]; timeouts [(2, 5)]; slowest (1650.9700121879578, (2, 6))  [12969.3s]
DONE
orbit 2: |S| = 21, |T'| = 71 (box), cells 306  [0.0s]
orbit 2 box case (0,1): GB size 170, dim 1, vdim -1  [673.5s]
orbit 2 box case (1,2): TIMEOUT 3600s  [5634.0s]
orbit 2 box case (1,5): TIMEOUT 3600s  [9666.5s]
orbit 3: |S| = 21, |T'| = 71 (box), cells 306  [0.0s]
orbit 3 box case (0,1): GB size 170, dim 1, vdim -1  [507.0s]
orbit 3 box case (1,2): TIMEOUT 3600s  [5111.5s]
orbit 3 box case (1,5): TIMEOUT 3600s  [9550.5s]
orbit 3 box case (2,5): TIMEOUT 3600s  [17274.3s]
orbit 3 box: nonempty cases [(0, 1)]; timeouts [(1, 2), (1, 5), (2, 5)]; slowest (2776.9764676094055, (2, 4))  [20101.2s]
DONE
orbit 4: |S| = 21, |T'| = 71 (box), cells 320  [0.0s]
orbit 4 box case (0,1): GB size 170, dim 1, vdim -1  [301.6s]
orbit 4 box case (1,2): TIMEOUT 3600s  [4430.8s]
orbit 4 box case (1,5): TIMEOUT 3600s  [8700.4s]
orbit 4 box case (2,5): TIMEOUT 3600s  [13994.3s]
orbit 4 box: nonempty cases [(0, 1)]; timeouts [(1, 2), (1, 5), (2, 5)]; slowest (1283.181254863739, (1, 7))  [18092.5s]
DONE
orbit 5: |S| = 21, |T'| = 71 (box), cells 320  [0.0s]
orbit 5 box case (0,1): GB size 170, dim 1, vdim -1  [173.0s]
orbit 5 box case (1,2): TIMEOUT 3600s  [4032.1s]
orbit 5 box case (1,5): TIMEOUT 3600s  [8428.8s]
orbit 5 box case (1,7): TIMEOUT 3600s  [12046.4s]
orbit 5 box case (2,5): TIMEOUT 3600s  [16606.8s]
orbit 5 box: nonempty cases [(0, 1)]; timeouts [(1, 2), (1, 5), (1, 7), (2, 5)]; slowest (648.140139579773, (1, 3))  [18737.4s]
DONE
orbit 6: |S| = 21, |T'| = 59 (box), cells 268  [0.0s]
orbit 6 box case (0,1): TIMEOUT 3600s  [3600.0s]
orbit 6 box case (0,2): TIMEOUT 3600s  [7200.0s]
orbit 6 box case (0,3): TIMEOUT 3600s  [10800.0s]
```

Representative 6 then ends with Sage's `Killed` line, and its Slurm log
reads `Detected 1 oom_kill event in StepId=598021.batch`. The number of
finished rows (`i = ... done` lines) is 21, 21, 1, 21, 21, 21 and 0 for
representatives 0 to 6. So:

| k | orbit size | `|T'|` | rows finished | nonempty | timeouts |
| --- | --- | --- | --- | --- | --- |
| 0 | 8 | 77 | 21 of 21 | `(0,1)` | `(2,5)` |
| 1 | 8 | 77 | 21 of 21 | `(0,1)` | none |
| 2 | 8 | 71 | 1 of 21 | `(0,1)` | `(1,2), (1,5)`; job cancelled at 12 h |
| 3 | 8 | 71 | 21 of 21 | `(0,1)` | `(1,2), (1,5), (2,5)` |
| 4 | 8 | 71 | 21 of 21 | `(0,1)` | `(1,2), (1,5), (2,5)` |
| 5 | 8 | 71 | 21 of 21 | `(0,1)` | `(1,2), (1,5), (1,7), (2,5)` |
| 6 | 4 | 59 | 0 of 21 | none seen | `(0,1), (0,2), (0,3)`; out of memory at 24G |

Only representative 1 has every case decided in this job. Representative 0 is
decided after the rerun in job 689435, task 0 (section below).

## Case `(0,1)` on `box(S)` without `u0` (job 599042, array `0-6`, 24G)

Mode `cases` sets `u_0 = 1` but keeps `u0` as a ring variable, which is why
case `(0,1)` above reports `dim 1, vdim -1`. The verify script recomputes
`I_01` over `Q` in `u1, ..., u20`, `v_h` for `h in T'`, and `w`. It computes
the length of the quotient and the characteristic polynomial `cp` of a random
linear form `L`, asserts that `cp` is squarefree of degree equal to the
length, writes every coordinate as a polynomial in `L`, evaluates it at the
roots of `cp` in `Q(zeta_8)`, and multiplies each `u` and `v` out in
`Q(zeta_8)[P]` with the group law. Verbatim, with the Singular warnings
removed:

```text
orbit 0: |S| = 21, |T'| = 77 (box), |T| = 21, GB size 138, dim 0  [1059.1s]
orbit 0: length 16, cp squarefree True, factor degrees over QQ [4, 4, 4, 4]  [1059.3s]
orbit 0: roots in QQ(zeta_8) 16 of 16, u v = 1 for all: True, inverse supported in T for all: True  [1060.3s]
DONE
orbit 1: |S| = 21, |T'| = 77 (box), |T| = 21, GB size 138, dim 0  [160.7s]
orbit 1: length 16, cp squarefree True, factor degrees over QQ [4, 4, 4, 4]  [161.2s]
orbit 1: roots in QQ(zeta_8) 16 of 16, u v = 1 for all: True, inverse supported in T for all: True  [162.1s]
DONE
orbit 2: |S| = 21, |T'| = 71 (box), |T| = 21, GB size 170, dim 0  [1116.9s]
orbit 2: length 16, cp squarefree True, factor degrees over QQ [4, 4, 4, 4]  [1117.5s]
orbit 2: roots in QQ(zeta_8) 16 of 16, u v = 1 for all: True, inverse supported in T for all: True  [1118.5s]
DONE
orbit 3: |S| = 21, |T'| = 71 (box), |T| = 21, GB size 170, dim 0  [423.2s]
orbit 3: length 16, cp squarefree True, factor degrees over QQ [4, 4, 4, 4]  [423.5s]
orbit 3: roots in QQ(zeta_8) 16 of 16, u v = 1 for all: True, inverse supported in T for all: True  [424.4s]
DONE
orbit 4: |S| = 21, |T'| = 71 (box), |T| = 21, GB size 170, dim 0  [297.5s]
orbit 4: length 16, cp squarefree True, factor degrees over QQ [4, 4, 4, 4]  [297.8s]
orbit 4: roots in QQ(zeta_8) 16 of 16, u v = 1 for all: True, inverse supported in T for all: True  [298.8s]
DONE
orbit 5: |S| = 21, |T'| = 71 (box), |T| = 21, GB size 170, dim 0  [181.0s]
orbit 5: length 16, cp squarefree True, factor degrees over QQ [4, 4, 4, 4]  [181.4s]
orbit 5: roots in QQ(zeta_8) 16 of 16, u v = 1 for all: True, inverse supported in T for all: True  [182.3s]
DONE
```

Task 6 hit the 6 h limit with no output (`CANCELLED ... DUE TO TIME LIMIT`).

## Resubmitted, not yet evidence (jobs 689435 and 689436)

Job 689435 runs `promislow-radius4-census-box-cases.py cases K box TL FILT`
from `sbox2.sbatch` (md5 `9ae3af42a45ce7ddc5b9c96423ed9e1e`; 96G, 3.5 days,
array `0-8%6`). The task list `sbox2_tasks.txt` (md5
`0748a6cb9100c3b97c5cab2b82b2887d`) reads, verbatim, one task per line as
`K TAG TL FILT`:

```text
0 hard 64800 only=2,5
3 hard 64800 only=1,2;1,5;2,5
4 hard 64800 only=1,2;1,5;2,5
5 hard 64800 only=1,2;1,5;1,7;2,5
2 hard 64800 only=1,2;1,5
6 hard 64800 only=0,1;0,2;0,3
2 sweep 3600 from=1
6 sweep 3600 from=1
6 row0 3600 only=0,4;0,5;0,6;0,7;0,8;0,9;0,10;0,11;0,12;0,13;0,14;0,15;0,16;0,17;0,18;0,19;0,20
```

Job 689436 reruns the verify script for representative 6 with 96G and a
3-day limit. Both were pending at submission. Nothing in this section is
used by any claim until its output is recorded here.


## Representative 0 decided (job 689435, task 0)

The support `S_0` of representative 0 of `census_pairs.json`, verbatim:

```text
[[[-1, -1, 1], [-3, 0, -1]], [[-1, -1, 1], [-1, -2, -1]], [[-1, -1, 1], [-1, 0, 1]], [[-1, -1, 1], [-1, 2, -1]], [[-1, -1, 1], [1, 0, -1]], [[-1, 1, -1], [-2, -1, -1]], [[-1, 1, -1], [-2, 1, 1]], [[-1, 1, -1], [0, -3, 1]], [[-1, 1, -1], [0, -1, -1]], [[1, -1, -1], [-3, 1, 0]], [[1, -1, -1], [-1, -1, 2]], [[1, -1, -1], [-1, 1, 2]], [[1, -1, -1], [1, -1, 0]], [[1, 1, 1], [-2, -2, -2]], [[1, 1, 1], [-2, -2, 0]], [[1, 1, 1], [-2, 0, -2]], [[1, 1, 1], [-2, 0, 0]], [[1, 1, 1], [0, -2, -2]], [[1, 1, 1], [0, -2, 0]], [[1, 1, 1], [0, 0, -2]], [[1, 1, 1], [0, 0, 0]]]
```

Its orbit has size 8 and its inverse support has word radius 5 (job 584612,
2026-09-12 artifact). Task 0 of job 689435 ran
`promislow-radius4-census-box-cases.py cases 0 box 64800 only=2,5`. On MSI the
script `sbox2.py` has md5 `1475fa8724be6a203bd5097b8552202d`, `sbox2.sbatch`
`9ae3af42a45ce7ddc5b9c96423ed9e1e`, `sbox2_tasks.txt`
`0748a6cb9100c3b97c5cab2b82b2887d`, `census_pairs.json`
`88d50831522fe612ef9412f27237bfb3` and `sbox_pairs.json`
`1e5080225b5f3600d58ea3a5df69951d`, matching the table above. Slurm:
`689435_0 uc0-sbox2 COMPLETED 03:15:09 0:0`. Output `sbox2_0_hard.out`, all 24
lines, verbatim (it has no warning lines):

```text
orbit 0: |S| = 21, |T'| = 77 (box), cells 338  [0.0s]
orbit 0 box: i = 0 done  [0.0s]
orbit 0 box: i = 1 done  [0.0s]
orbit 0 box: i = 2 done  [11689.4s]
orbit 0 box: i = 3 done  [11689.4s]
orbit 0 box: i = 4 done  [11689.4s]
orbit 0 box: i = 5 done  [11689.4s]
orbit 0 box: i = 6 done  [11689.4s]
orbit 0 box: i = 7 done  [11689.4s]
orbit 0 box: i = 8 done  [11689.4s]
orbit 0 box: i = 9 done  [11689.4s]
orbit 0 box: i = 10 done  [11689.4s]
orbit 0 box: i = 11 done  [11689.4s]
orbit 0 box: i = 12 done  [11689.4s]
orbit 0 box: i = 13 done  [11689.4s]
orbit 0 box: i = 14 done  [11689.4s]
orbit 0 box: i = 15 done  [11689.4s]
orbit 0 box: i = 16 done  [11689.4s]
orbit 0 box: i = 17 done  [11689.4s]
orbit 0 box: i = 18 done  [11689.4s]
orbit 0 box: i = 19 done  [11689.4s]
orbit 0 box: i = 20 done  [11689.4s]
orbit 0 box (only [(2, 5)], from 0): nonempty cases []; timeouts []; slowest (11689.366257429123, (2, 5))  [11689.4s]
DONE
```

With job 598021 task 0 (21 of 21 rows, only `(0,1)` nonempty, only `(2,5)` at
the limit) this decides all 210 cases for representative 0. Job 599042 task 0
checked case `(0,1)`. This is the evidence for
`research/promislow-radius4-orbit0-units-need-zeta8-any-inverse.md`.

### Status of the other tasks at the time of this harvest

`squeue` and `sacct` at harvest time: tasks 1 to 5 of 689435 (the hard cases
of representatives 3, 4, 5, 2 and 6) and task 6 of 689436 (representative 6)
running, elapsed `3:49:31`; task 6 of 689435 (representative 2 sweep)
running, elapsed `33:02`; tasks 7 and 8 (representative 6 sweep and row 0)
pending. `sbox2_2_hard.out`, `sbox2_3_hard.out`, `sbox2_4_hard.out`,
`sbox2_5_hard.out` and `sbox2_2_sweep.out` hold the header line and
`i = 0 done`; `sbox2_6_hard.out` holds only the header line;
`sboxv.689436_6.log` is empty. So nothing else is decided yet.

| k | decided | still open |
| --- | --- | --- |
| 0 | all 210 cases; `(0,1)` checked (599042) | none |
| 1 | all 210 cases; `(0,1)` checked (599042) | none |
| 2 | row 0; `(0,1)` checked (599042) | `(1,2), (1,5)` running (task 4); rows 1 to 20 running (task 6) |
| 3 | all rows except the timeouts; `(0,1)` checked (599042) | `(1,2), (1,5), (2,5)` running (task 1) |
| 4 | all rows except the timeouts; `(0,1)` checked (599042) | `(1,2), (1,5), (2,5)` running (task 2) |
| 5 | all rows except the timeouts; `(0,1)` checked (599042) | `(1,2), (1,5), (1,7), (2,5)` running (task 3) |
| 6 | nothing | `(0,1), (0,2), (0,3)` running (task 5); `(0,4)` to `(0,20)` pending (task 8); rows 1 to 20 pending (task 7); `(0,1)` check running (689436 task 6) |

### Cancellation (2026-09-13 17:44:22)

Every remaining task was cancelled in the same second by uid 81060, which is
`sauer354`, the account the jobs run under. Nothing in the job directory
gives a reason. `sacct -j 689435,689436 -X -o JobID,State,Elapsed,End -P`,
verbatim:

```text
JobID|State|Elapsed|End
689435_0|COMPLETED|03:15:09|2026-09-13T16:22:31
689435_1|CANCELLED by 81060|04:37:00|2026-09-13T17:44:22
689435_2|CANCELLED by 81060|04:37:00|2026-09-13T17:44:22
689435_3|CANCELLED by 81060|04:37:00|2026-09-13T17:44:22
689435_4|CANCELLED by 81060|04:37:00|2026-09-13T17:44:22
689435_5|CANCELLED by 81060|04:37:00|2026-09-13T17:44:22
689435_6|CANCELLED by 81060|01:20:31|2026-09-13T17:44:22
689435_8|CANCELLED by 81060|00:00:00|2026-09-13T17:44:22
689436_6|CANCELLED by 81060|04:37:00|2026-09-13T17:44:22
```

Task 7 has no line of its own in `sacct`, and `squeue` lists no job for these
cases. `sbox2.done` still reads only `JOBDONE 0 0 hard`. The only new output
line is `orbit 2 box case (1,2): TIMEOUT 3600s  [3600.0s]` in
`sbox2_2_sweep.out`, and it decides nothing. No task finished a row past
`i = 0`. So the table above stands, except that every case listed as running
or pending is now unrun: representatives 2 to 6 remain undecided on the box,
and representative 6 has no `(0,1)` check.
