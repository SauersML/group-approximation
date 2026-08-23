# Same-core fourth-power gauge-gap audit

This audit reconstructs the finite model behind the proposed aggregate
Iwahori estimate and distinguishes the proved gauge-only Fox calculation
from the transverse endpoint motion which refutes the aggregate claim. The reproducible
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

## Full endpoint cancellation and the refuting conjugation packet

The preceding SVD restricts the tangent itself to `{T}'`. It therefore does
not test whether a commutant component is canceled by a transverse endpoint
tangent. The `--full-selector` audit prescribes the regular `{T}'`
projection of an arbitrary matrix tangent, minimizes all row derivatives
over its orthogonal complement, and reports the remaining quotient gap.
The difference is decisive:

| projective endpoint | max orbit | first two rows | three torsion rows | all four endpoint rows |
|---|---:|---:|---:|---:|
| `p=5` | 2 | 0 | 0.381966 | 2.526255 |
| `p=7` | 3 | 0 | 0.635950 | 2.182619 |
| `p=11` | 5 | 0 | 0.919431 | 1.544443 |
| `p=19` | 9 | 0 | 0.475972 | 0.917944 |
| `p=23` | 11 | 0 | 0.473472 | 0.767130 |
| `p=31` | 5 | 0 | 0.736124 | 1.583378 |

The zero in the first pair has an exact explanation. If `z in {T}'`, then

```text
X_z=zXz^(-1)
```

still has `X_z^2=(X_zT)^3=1`. The other two rows cost only the commutator
of `z` with `R`. Choosing a first Koopman mode produces the following MSI
values; the last column is the minimum projected coboundary-preimage norm
divided by the root-sum-square of all four endpoint row defects.

| `p` | max orbit `L` | Koopman gap | preimage/row ratio |
|---:|---:|---:|---:|
| 7 | 3 | 1.732051 | 0.278119 |
| 11 | 5 | 1.175571 | 0.378926 |
| 19 | 9 | 0.684040 | 0.640643 |
| 23 | 11 | 0.563465 | 0.795483 |
| 47 | 23 | 0.272333 | 1.641515 |
| 59 | 29 | 0.216238 | 2.111657 |
| 83 | 41 | 0.153099 | 2.912470 |
| 107 | 53 | 0.118481 | 3.779510 |

The ratio grows linearly in `L`; the preserved rows were below `5e-15` in
every run. This numerical family is subsumed by the exact left-regular
proof in `endpoint-conjugation-refutes-iwahori-energy`, which gives row
energy at most `13 epsilon^2 g_L^2` and weighted inverse energy at least
`epsilon^2/32`.

Thus the gauge-only Fox floor remains correct, but the frozen-core aggregate
claim and its row-tame selector are false. The strongest surviving
finite-dimensional target is `uniform-gauge-optimized-induced-energy`:
moving the exact core by the same conjugation makes this counterpacket an
exact endpoint at cost `O(epsilon^2g_L^2)`.
