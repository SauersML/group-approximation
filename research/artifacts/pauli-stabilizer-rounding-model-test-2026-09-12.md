# Model test of stabilizer rounding for Pauli sums (2026-09-12)

Lane `ex-quantum-pcp`. The test is a check on an unreviewed theorem, not part of
its proof. The proof is in
`research/artifacts/pauli-frustration-stabilizer-rounding-2026-09-12.md`.

## What was run

Script: `research/artifacts/check-pauli-stabilizer-rounding-2026-09-12.py`, run on
MSI (sioux node) with `/usr/bin/python3.12` and numpy 2.2.6. Runtime was under
one minute.

- It enumerates all stabilizer states on `n` qubits by breadth-first search from
  `|0^n>` under `H`, `S` and `CNOT`, up to global phase. The counts found are
  6, 60 and 1080 for `n=1,2,3`, the known numbers.
- It draws random Pauli sums: 1 to 8 terms with uniform coefficients in `[-1,1]`.
  Half the instances are biased toward low frustration, adding 1 to 4 terms of
  coefficient `1` and scaling the rest by `0.2`.
- For each instance it computes `lambda_max` by exact diagonalization and
  `stab_max` by maximizing over all stabilizer states. It checks
  `stab_max >= lambda_max - (1+sqrt2)(W - lambda_max)` with tolerance `1e-9`, and
  records the largest ratio `(lambda_max - stab_max)/(W - lambda_max)`.

## Output (verbatim)

```text
n=1 stabilizer_states=6 trials=3000 violations=0 worst_ratio=0.707107
  worst instance: ([('X', 1.0), ('Z', 1.0), ('I', 1.0), ('I', 1.0), ('I', 0.12562095654605474)], 3.5398345189191502, 3.125620956546055, 4.125620956546054)
n=2 stabilizer_states=60 trials=3000 violations=0 worst_ratio=0.707107
  worst instance: ([('ZY', 1.0), ('YX', 1.0), ('ZZ', 1.0), ('II', 0.09923065668991021)], 2.5134442190630057, 2.09923065668991, 3.0992306566899104)
n=3 stabilizer_states=1080 trials=1500 violations=0 worst_ratio=0.707107
  worst instance: ([('IZX', 1.0), ('IXI', 1.0), ('XII', 1.0), ('XXY', -0.007400291389218161)], 2.4216138537623135, 2.0074002913892173, 3.007400291389218)
DONE_SRCHECK
```

## Reading

- No violation of (SR) in 7500 instances.
- The largest observed ratio is `0.707107 = 1/sqrt2` at every size. It is attained
  by one anticommuting pair of equal weight plus terms that commute with a
  stabilizer choice (identity padding, or `ZZ` commuting with `ZY` and `YX`).
  This is the one-qubit example `(X+Z)/2` of the artifact.
- Random search at `n<=3` is weak evidence about the optimal constant. It does not
  prove that `1/sqrt2` is the supremum; see the open claim
  `stabilizer-rounding-constant-is-one-over-sqrt2`.
