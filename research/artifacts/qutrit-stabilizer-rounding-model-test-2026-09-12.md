# Model test of qudit stabilizer rounding at d=3 (2026-09-12)

Lane `ex-quantum-pcp`. This checks an unreviewed theorem; it is not part of the proof.
The proof is in `research/artifacts/qudit-stabilizer-rounding-2026-09-12.md`.

## What was run

Script: `research/artifacts/check-qutrit-stabilizer-rounding-2026-09-12.py`, run on
MSI (sioux node) with `/usr/bin/python3.12` and numpy 2.2.6, in under a minute.

- It enumerates all qutrit stabilizer states for `n=1,2` by breadth-first search from
  `|0^n>` under the Fourier gate, the phase gate `diag(1,1,omega)` and `SUM`, up to
  global phase. The counts found are 12 and 360, the known numbers `d(d+1)` and
  `d^2 (d+1)(d^2+1)`.
- It draws random Hermitian Weyl sums `K = sum_j (c_j g_j + conj(c_j) g_j^dagger)` with
  1 to 6 terms. Half the instances are biased toward `c_j` near `1` (low
  frustration). The weight is `W = sum_j 2|c_j|`.
- For each instance it computes `lambda_max` exactly and `stab_max` over all
  stabilizer states. It checks
  `stab_max >= lambda_max - C_3(W - lambda_max)` with `C_3 = 8/sin^2(pi/3) - 1`, and
  records the largest ratio `(lambda_max - stab_max)/(W - lambda_max)`.

## Output (verbatim)

```text
d=3 n=1 stabilizer_states=12 trials=3000 violations=0 worst_ratio=0.573544 C3=9.6667
  worst instance: ([(((0,), (0,)), (1.024704548198883+0.020065542324303444j)), (((0,), (2,)), (0.9475609528872125+0.07339679850086867j)), (((2,), (2,)), (0.9497617357046277+0.016297674176385057j))], 4.642003477281053, 3.948932567807023, 5.850403713753897)
d=3 n=2 stabilizer_states=360 trials=1500 violations=0 worst_ratio=0.574563 C3=9.6667
  worst instance: ([(((2, 2), (2, 2)), (1.0253347981760077+0.017138902127125568j)), (((1, 2), (2, 2)), (1.0232128937971003+0.0627918169821217j))], 2.7989258422945253, 2.050669596352018, 4.101231591353313)
DONE_QUTRIT
```

## Reading

- No violation in 4500 instances.
- The largest observed ratio is about `0.57`, far below `C_3 = 9.67`. The constant from
  the norm argument is loose at `d=3`; no sharp value is claimed.
- The worst instances are two or three non-commuting Weyl operators of nearly equal
  weight, the qutrit analogue of the qubit `X+Z` example.
