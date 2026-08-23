# Same-core fourth-power gauge-gap audit

This audit reconstructs the finite model behind the proposed aggregate
Iwahori estimate and distinguishes the proved Fox-differential calculation
from the still-open nonlinear endpoint-selection problem.  The reproducible
implementation is `experiments/iwahori_cycle_gauge_gap.py`; all reported
runs used one BLAS thread through the MSI wrapper on `acn112`.

## Exact model and quotient operator

For each odd prime `p`, the matrices

```text
x=[[0,-1],[1,0]],   r=diag(2,1/2),   t=[[1,1],[0,1]]
```

act by permutations on `P^1(F_p)` and satisfy the five square-free Iwahori
words exactly.  On the full commutant `Z={T}'`, the script forms the
normalized-HS orthonormal matrix-unit basis of every `T`-eigenspace,
including the multiplicity-two eigenvalue-one block.  For heterogeneous
direct sums it retains all cross-summand matrix units at coincident
eigenvalues.

Under `X_epsilon=exp(epsilon A)X`, it constructs exactly

```text
L_x2 A = A+Ad(X)A,
L_xr2 A = A+Ad(XR)A,
L_xt3 A = sum_(j=0)^2 Ad((XT)^j)A,
L_xt2r3 A = sum_(j=0)^2 Ad((XT^2R)^j)A,
D A = A-Ad(R^(-1))A.
```

The SVD is taken only after restricting to `ker(D)^perp`.  On this quotient,
`D^dagger D=1`, so the denominator is the exact inverse-Koopman energy, not
the unweighted residual norm.

## Reproduced values

All five exact word defects were zero to machine precision.  The following
table gives the maximum nontrivial fourth-power orbit length and quotient
smallest singular values.  `two rows` means `(x^2,(xt)^3)`, `cubics` means
the two cubic rows, and `all` means all four rows containing `x`.

| endpoint block | max orbit | regular quotient dim | two rows | cubics | all |
|---|---:|---:|---:|---:|---:|
| `p=7` | 3 | 4 | 1.405804 | 1.931894 | 2.641266 |
| `p=11` | 5 | 8 | 1.608698 | 1.752959 | 2.469242 |
| `p=19` | 9 | 16 | 1.778953 | 1.847441 | 2.559437 |
| `p=23` | 11 | 20 | 1.825345 | 1.897151 | 2.607472 |
| `p=47` | 23 | 44 | 1.957825 | 2.065411 | 2.772706 |
| `p=59` | 29 | 56 | 1.989595 | 2.108765 | 2.815881 |
| `p=83` | 41 | 80 | 2.030243 | 2.164877 | 2.872094 |
| `p=107` | 53 | 104 | 2.055872 | 2.200444 | 2.907910 |
| `p=7 direct-sum p=11` | 5 | 12 | 1.405804 | 1.752959 | 2.469242 |
| `p=47 direct-sum p=47` | 23 | 176 | 1.957825 | 2.065411 | 2.772706 |
| `p=7 direct-sum p=11 direct-sum p=19` | 9 | 28 | 1.405804 | 1.752959 | 2.469242 |

The largest operator-norm error in the numerical identity
`D^dagger D=1` on the reported regular quotient was below `1.6e-13`.
There is no downward cycle-length trend; amplification and heterogeneous
cross-block gauges inherit the minimum component value in these tests.

These values are diagnostics, not the proof of a floor.  The exact identity

```text
A=L_xt3 A-Ad(XT)(L_x2 A)
```

proves the universal floor `1/sqrt(2)` and explains the computation.  This
identity does not use either baseline equation `X^2=1` or `(XT)^3=1`, so the
same floor holds at approximate and nonextendable extenders as well.

## Outlier audit

The known compressed even-Weil packets are the relevant outlier extenders:
they have an exact BS core, exact involution and inversion rows, and cubic
defect of order `p^(-1/2)`, while same-dimensional exact extension fails.
Their projected Weyl/inversion residual is exactly zero, so their
inverse-Koopman numerator is zero.  They neither degrade nor test the
same-core quotient gap.  Direct Schrödinger-model probes confirm the stronger
tangent statement:

| compressed outlier | max orbit | regular quotient dim | two rows | cubics | all | cubic defect |
|---|---:|---:|---:|---:|---:|---:|
| `p=17` | 4 | 6 | 1.433398 | 1.777877 | 2.509895 | 0.471257 |
| `p=41` | 10 | 18 | 1.742572 | 2.094963 | 2.810584 | 0.347743 |
| `p=73` | 9 | 32 | 1.907527 | 2.190510 | 2.909420 | 0.276941 |
| `p=89` | 11 | 40 | 1.947846 | 2.214879 | 2.930882 | 0.255129 |

Here the BS, involution, and inversion defects were below `3e-14`; the two
displayed cubic defects agree to the shown precision and decay at the known
rank-one-boundary scale.  The quotient Jacobian does not decay with them.
The outliers instead show why the missing global theorem is selection of an
exact endpoint after flexible boundary padding.

Thus the finite-cycle singular-value problem is completely controlled at
every unitary over an exact core.  A counterexample to the global aggregate
claim must exploit nonlinear normalized-HS geometry or flexible endpoint
selection; it cannot arise as a degenerating Fox singular value along long
Fourier cycles, heterogeneous direct sums, or the existing compressed Weil
boundary packets.
