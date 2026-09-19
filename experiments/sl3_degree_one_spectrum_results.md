# Degree-one repair spectrum on fixed `SL_3(Z)` charts

Date: 2026-08-11

## Question

The degree-zero experiment in `phase_code_spectrum_results.md` shows that
arbitrary locally free Schreier charts can have vanishing repair gap.  The
next live TRUE question is whether a fixed property-`(T)` presentation can
instead supply a degree-one linear repair estimate.

`sl3_degree_one_spectrum.py` tests this on the reduction actions

`X_p = F_p^3 - {0}`

of a fixed six-generator presentation of `SL_3(Z)`.  The generators are the
six elementary transvections.  The 13 relators are the six Steinberg
commutator relations, the six displayed commuting-root commutators, and the
Conder--Robertson--Williams torsion relation

`(x_12 x_21^(-1) x_12)^4 = 1`.

For the resulting finite presentation complex the program constructs the
sparse cellular coboundaries

`d0:C^0 -> C^1`, `d1:C^1 -> C^2`

and measures the bottom of

`Delta_1 = d1^* d1 + d0 d0^*`.                         `(SDO1)`

The construction checks every relator modulo `p` and checks `d1 d0=0`
exactly before diagonalization.

## MSI run

The runs used the existing Anaconda NumPy/SciPy installation on `acn116`,
four CPU cores, and sparse ARPACK diagonalization.  No package build and no
RAM-backed temporary directory were needed.  There are no surviving jobs.

The complete machine-readable outputs are:

* `sl3-degree-one-spectrum.jsonl`;
* `sl3-degree-one-spectrum-extra.jsonl`;
* `sl3-degree-one-spectrum-large.jsonl`;
* `sl3-degree-one-low-modes.jsonl`;
* `sl3-character-block-validation.jsonl`;
* `sl3-character-block-existing-primes.jsonl`;
* `sl3-character-block-all.jsonl`;
* `sl3-character-block-targets.jsonl`;
* `sl3-character-block-structure.jsonl`.

The first positive degree-zero singular value and the least degree-one
Hodge singular value were:

| `p` | vertices | edges | cells | `sigma_1(d0)` | `sqrt(lambda_min(Delta_1))` |
|---:|---:|---:|---:|---:|---:|
| 3  | 26    | 156     | 338     | 1.645751 | 1.000000 |
| 5  | 124   | 744     | 1,612   | 1.329473 | 1.000000 |
| 7  | 342   | 2,052   | 4,446   | 1.213558 | 1.000000 |
| 11 | 1,330 | 7,980   | 17,290  | 1.081600 | 0.986762 |
| 13 | 2,196 | 13,176  | 28,548  | 1.047932 | 0.980771 |
| 17 | 4,912 | 29,472  | 63,856  | 1.012725 | 0.979245 |
| 19 | 6,858 | 41,148  | 89,154  | 0.992815 | 0.962999 |
| 23 | 12,166 | 72,996 | 158,158 | 0.967616 | 0.767843 |
| 29 | 24,388 | 146,328 | 317,044 | 0.953613 | 0.890685 |
| 31 | 29,790 | 178,740 | 387,270 | 0.961326 | 0.899509 |
| 37 | 50,652 | 303,912 | 658,476 | 0.942777 | 0.815371 |

Thus the coexact degree-one bottom stays between `0.7678` and `1` over the
measured family, while the complexes grow by nearly four orders of
magnitude.  This is positive evidence for a linear repair estimate on these
selected charts, but it is not a proof of a uniform lower bound.  The dip at
`p=23` also makes extrapolation from a smooth trend unjustified.

## The low modes have exact scalar-character structure

Scalar multiplication by `F_p^*` commutes with the `SL_3(F_p)` action and
therefore with `(SDO1)`.  The `--analyze` mode Fourier-transforms a lowest
eigenvector along this scalar action.  Two diagnostic cases give:

| `p` | `lambda_min(Delta_1)` | `||d1 u||^2` | `||d0^* u||^2` | scalar character |
|---:|---:|---:|---:|---|
| 23 | 0.589583616965 | 0.589583616965 | `2.32e-19` | quadratic (`j=11`) |
| 37 | 0.664830486617 | 0.664830486617 | `1.23e-18` | trivial (`j=0`) |

In both cases the reported character has Fourier weight `1` to numerical
precision.  The low vector is also coexact to numerical precision: all of
its Hodge energy is `||d1 u||^2`, not `||d0^*u||^2`.

This is the useful output of the experiment.  The full operator decomposes
into `p-1` scalar-character blocks.  The `p=23` anomaly is not an
unstructured large-dimensional near-kernel; it is a quadratic-character
block.  The `p=37` low mode descends to the projective-plane quotient.

## Exact block construction and validation

`sl3_character_block_spectrum.py` now performs this Fourier reduction
directly.  It records every transition as a projective target, a sign, and
an integer exponent modulo `p-1`.  Roots of unity are evaluated only after a
character is selected.  Relation paths close both projectively and in their
integer scalar exponent before any eigensolver is called.

At `p=5`, the union of block minima begins

`1, 1, 1.311018630490, 1.334178582518, ...`,

which reproduces the full operator.  At the two large diagnostic primes the
reduced blocks reproduce the full global minima to about `1e-14`:

* `p=23`, quadratic character: `0.589583616964886`;
* `p=37`, trivial character: `0.664830486617010`.

The reduction is substantial.  At `p=37`, the full degree-one space has
303,912 coordinates; one exact character pattern has 8,442 edge coordinates
and 92,862 relator terms, and diagonalizes in well under two seconds on the
four-core run.

An all-character pass on the already measured primes gives the following
winning sectors.  Character `j` means the character sending the chosen
primitive root to `exp(2 pi i j/(p-1))`.

| `p` | winning `j` | character order | least Hodge eigenvalue |
|---:|---:|---:|---:|
| 3  | 0  | 1  | 1.000000000000 |
| 5  | 0  | 1  | 1.000000000000 |
| 7  | 0  | 1  | 1.000000000000 |
| 11 | 3  | 10 | 0.973698887134 |
| 13 | 7  | 12 | 0.961911228508 |
| 17 | 11 | 16 | 0.958921109237 |
| 19 | 13 | 18 | 0.927367584903 |
| 23 | 11 | 2  | 0.589583616965 |
| 29 | 5  | 28 | 0.793320605152 |
| 31 | 15 | 2  | 0.809116176894 |
| 37 | 0  | 1  | 0.664830486617 |

Every winning mode is coexact numerically.  However, the winning character
is not confined to the trivial and quadratic sectors: primitive characters
win for several primes.  Any uniform proof must therefore control all
characters, not extrapolate only the two initially recognized blocks.

The low-mode structure diagnostics show a repeated local pattern.  At
`p=23` and `p=37` the six generator energies are close to uniform, and the
Steinberg/commuting-root relators carry nearly all the coexact energy.  The
single torsion relator contributes only `0.0004414` and `0.0002257`,
respectively.  This was the signal to search for one fixed group-ring
inequality instead of extending the prime table.

## Exact quantitative resolution

The certificate miner succeeded.  `sl3_group_ring_sos.py` constructs the
Hodge operator as a `6 x 6` matrix over `R[SL_3(Z)]`.  A radius-zero Gram SDP
found a positive candidate, and `sl3_sos_certificate.py` rationalized it and
paid for the complete exact coefficient residual.  The resulting rigorously
verified inequality is

`Delta_1 >= 0.0028329113480286 I`

for every unitary representation, not just the finite `X_p` actions.  The
exact rational theorem, certificate hash, proof, and robust-repair corollary
are in `notes/TRUE_SL3_HODGE_SOS.md`.

## Analytic resolution of the immediate candidate

The uniform real-linear gap is now proved without further computation in
`notes/TRUE_PROPERTY_T_LINEAR_COCYCLE_GAP.md`.  For a fixed finite
presentation of any property-`(T)` group, a Hilbert-ultraproduct argument and
Delorme--Guichardet vanishing give a positive lower bound for the coexact
singular value over **every exact unitary representation**.  It applies in
particular to all permutation representations on `X_p`.

The group-ring certificate above supplies an explicit constant
simultaneously for all representations.  The proof-producing successor is
instead nonlinear: control the
integral carries created by logarithms of circle phases, and explain how the
selected exact-action gap survives the approximately multiplicative charts
with the required relatively-Haar statistics.  Those are exactly the parts
not supplied by property `(T)`.

## Reproduction

On a compute node with NumPy and SciPy already available:

```text
python experiments/sl3_degree_one_spectrum.py --primes 3 5 7 11
python experiments/sl3_degree_one_spectrum.py --primes 23 37 --eigenvalues 2 --analyze
```

The program writes one JSON object per prime to standard output.  Redirect
that output to shared storage, not a RAM-backed temporary directory.
