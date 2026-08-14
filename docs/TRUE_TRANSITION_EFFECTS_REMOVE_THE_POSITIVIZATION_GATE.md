# Intrinsic transition effects remove the positivization gate

Date: 2026-08-14

## 1. Outcome

The operator-valued coefficients of a group-algebra gauge need not be
positive, which prevented direct use of cardinality-free POVM
orthogonalization. There is a more intrinsic coefficient family which is
positive automatically.

Let `P` be a source spectral projection, let `(Q_j)` be a target spectral
PVM, and let `U` be the actual compressor matrix. Define the transition
effects in the corner `PMP` by

```text
A_j=P U* Q_j U P.                                    (TER1)
```

Then `(A_j)` is a POVM. Its total non-idempotence is exactly half the total
commutator energy of the transported source projection `E=UPU*` against the
target PVM:

```text
sum_j tau_P(A_j-A_j^2)
 =1/(2 tau(P)) sum_j ||[E,Q_j]||_2^2.                (TER2)
```

Consequently de la Salle's theorem rounds `(A_j)` to a PVM with total
squared Hilbert--Schmidt error bounded by

```text
sum_j ||A_j-R_j||_2^2
 <(9/2) sum_j ||[E,Q_j]||_2^2.                       (TER3)
```

The estimate is independent of the number of target characters and the
matrix dimension. Thus positivity is no longer a separate gate in the
growing-envelope program. The remaining task is exactly the one already
isolated by the binary decoder: prove that the transported source projection
has vanishing total commutator/conditional-variance energy against the
target fiber PVM.

## 2. The transition family is a POVM

Let `(M,tau)` be a finite tracial matrix algebra, let `P` be a nonzero
projection, let `U` be unitary, and let `(Q_j)_(j in J)` be a finite PVM:

```text
Q_j Q_k=0  (j!=k),       sum_j Q_j=1.                (TER4)
```

Every operator in `(TER1)` is positive because

```text
A_j=(Q_j U P)*(Q_j U P).                             (TER5)
```

Moreover

```text
sum_j A_j
 =P U*(sum_j Q_j)U P
 =P.                                                  (TER6)
```

Therefore `(A_j)` is a positive operator-valued measure in the unital
corner `PMP`. No choice of matrix units, extension-character representatives,
or polar decompositions occurs in its definition.

Changing a redundant tensor identification inside a chart commutant leaves
the ambient projections `P,Q_j` and the actual group-word matrix `U`
unchanged, so it leaves `(A_j)` unchanged. These effects are intrinsic to
the represented finite packet, unlike coefficients obtained by expanding a
chosen commutant gauge in a regular basis.

## 3. Exact variance--commutator identity

Put

```text
E=U P U*.                                              (TER7)
```

Trace cyclicity gives

```text
tau(A_j)=tau(Q_j E),
tau(A_j^2)=tau(Q_j E Q_j E).                          (TER8)
```

Because `E` and `Q_j` are projections,

```text
||[E,Q_j]||_2^2
 =2[tau(E Q_j)-tau(E Q_j E Q_j)].                    (TER9)
```

Sum `(TER8)--(TER9)` over `j` and use `sum_j Q_j=1`:

```text
sum_j tau(A_j-A_j^2)
 =tau(P)-sum_j tau(Q_j E Q_j E)
 =(1/2)sum_j ||[E,Q_j]||_2^2.                       (TER10)
```

After normalizing the corner trace by

```text
tau_P(X)=tau(X)/tau(P),                               (TER11)
```

equation `(TER10)` is exactly `(TER2)`. Equivalently,

```text
tau_P(sum_j A_j^2)
 =1-1/(2tau(P))sum_j||[E,Q_j]||_2^2.                 (TER12)
```

This is a total-error Parseval identity. There is no minimum atom mass and
no sum-to-maximum conversion.

## 4. Cardinality-free PVM rounding

Apply Theorem 1.2 of Mikael de la Salle's
[Orthogonalization of Positive Operator Valued Measures](https://arxiv.org/abs/2103.14126)
to the corner POVM `(A_j)`. If

```text
epsilon
 =1-tau_P(sum_j A_j^2)
 =1/(2tau(P))sum_j||[E,Q_j]||_2^2,                  (TER13)
```

there is a PVM `(R_j)` in `PMP` such that

```text
sum_j ||A_j-R_j||_(2,tau_P)^2 <9 epsilon.            (TER14)
```

Multiplying by `tau(P)` gives `(TER3)`. In particular, even when the finite
character envelope grows, vanishing **total** commutator energy produces a
nearby exact transition PVM with no cardinality loss.

The theorem rounds the quantum transition at each source corner. Shared
marginals and multiplication coherence must still be retained when these
corner PVMs are assembled into whole response maps; `(TER3)` does not assert
that independently rounded corners are automatically compatible.

## 5. Binary specialization

For a binary target PVM `(Q_0,Q_1)`, the two effects are

```text
A_0=P-A_1.                                             (TER15)
```

Their non-idempotence is the operator version of conditional branch
variance. If the target PVM is the extension-character PVM and `P` is one
coarse source-character atom, summing `(TER10)` over source atoms recovers
the variance measured in
`TRUE_BINARY_EXTENSION_FIBER_MAJORITY_DECODER.md`. Fiberwise majority is
the commutative shadow of rounding the two-outcome POVM.

For an actual unitary compressor satisfying approximate covariance, one
already has

```text
sum_j ||[U P U*,Q_j]||_2^2 ->0                       (TER16)
```

for the named compressor/source/target projections. The estimate is
dimension-free: Fourier averaging gives
the transported source projection within the covariance RMS error of the
coarse target Fourier cut, which is a sum of fine target cuts. Hence

```text
sum_j ||[U P U*,Q_j]||_2^2
 <=2 (covariance RMS defect)^2.                      (TER16a)
```

See `TRUE_COVARIANCE_CONTROLS_TOTAL_TRANSITION_VARIANCE.md`. Thus every
single compressor edge already supplies an asymptotically exact fine-outcome
PVM after rounding.

## 6. Exact remaining gate

The advance is a change of coefficient model:

```text
arbitrary group-algebra coefficients
  -> positivity problem,

intrinsic transition effects P U*Q_j U P
  -> automatic POVM + exact variance identity.       (TER17)
```

Positivity, PVM rounding, extension-fiber representatives, source gauge, and
the single-edge estimate `(TER16)` are all closed. What remains is
compatibility between the separately obtained transition PVMs. Different
adjacent-root occurrences may produce noncommuting measurements or labels
which do not obey the multiplication table on one common multiplicity
coordinate.

The mixed atlas theorem must therefore make the finite family of rounded
PVMs jointly multiplication-compatible, with total error tending to zero.
Only then can character-to-map coarsening, tree gluing, and the robust
`1/36` paired-quotient floor apply. The fixed Pauli model is the calibration:
it realizes every single-edge transition PVM exactly while keeping the
different edge measurements quantum-incompatible. No nonhyperlinear group
is claimed before this multi-edge compatibility estimate is established.
