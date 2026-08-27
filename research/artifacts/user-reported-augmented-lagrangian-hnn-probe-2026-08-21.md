# User-reported augmented-Lagrangian HNN probe

Date: 2026-08-21.

Status: **reported heuristic, not rerun or independently verified**. The
numerical table and experiment descriptions below were supplied by the user.
No optimizer state, implementation, normalization audit, or lower-bound
certificate was supplied with this ingestion.

## Reported objective

The experiment reportedly minimizes the sum of squared normalized
Hilbert--Schmidt defects of the defining relators, using an
augmented-Lagrangian constraint

```text
||w-I||_2^2 >= 1.                                      (UAL1)
```

Thus a small reported floor is intended to mean that the presentation has a
low-defect finite-dimensional tuple while the marked word is forced to stay
separated. This is a nonconvex constrained optimization diagnostic, not a
proof that such tuples exist asymptotically.

## Reported calibrations and controls

- **BS(2,3) calibration:** the report labels the marked word “the trivial
  word `(relator)^2`” and gives a floor of approximately `.27`.
- **BS(2,3) control:** with `w=[tat^(-1),a]`, the report gives defect `.004`
  in dimensions `8` through `16`.

The first label is ambiguous and should not be endorsed literally without the
code. If `(relator)^2` is the square of a defining relator, then forcing
`(UAL1)` makes the zero-defect locus infeasible, so a positive optimization
floor is qualitatively expected; however, the value `.27` cannot be checked
without knowing whether “floor” is the summed squared objective, a maximum
defect, or an RMS normalization. The phrase “as it must be” in the source
report is therefore retained only as calibration intent, not as a verified
mathematical consequence with that numerical constant.

## Reported projective HNN table

The candidate is

```text
Gbar_2=<PSL_2(Z[1/2]),t | [t,PSL_2(Z)]=1>,
w=[t,r],                                                (UAL2)
```

with congruence seeds from the action on `P^1(F_p)`. The supplied component
labels are `base`, `t`, and `cyclic-HNN`; their sum agrees with `floor` up to
the displayed rounding.

| `p` | `d` | floor | base | `t` | cyclic-HNN |
|---:|---:|---:|---:|---:|---:|
| 7  | 8  | .076 | .015 | .061 | .0000 |
| 11 | 12 | .055 | .008 | .047 | .0001 |
| 13 | 14 | .048 | .008 | .040 | .0004 |
| 17 | 18 | .048 | .008 | .040 | — |
| 23 | 24 | .070 | .009 | .062 | — |
| 31 | 32 | .076 | .016 | .060 | — |

The report additionally states:

- random starts gave a base-alone floor in the range `.2`--`.3`;
- the optimized base moved normalized-HS distance approximately `.4` from
  the exact congruence seed;
- the run used one CPU and dimensions at most `32`;
- the anticipated asymptotic signal is `O(p^(-1/2))`, but the report expects
  its visible regime only around `p` of order `10^4`.

## Interpretation boundary

The six displayed floors are nonmonotone and do not establish the reported
`p^(-1/2)` law. They could reflect local minima, seed dependence, component
tradeoffs, or the small-prime regime. Conversely, their failure to decrease
over this range does not refute a crossover predicted only at much larger
prime.

Most importantly, this is a different experiment from
`psl2-far-sector-optimizer-heuristic-2026-08-21`. The older `d=6` smoke probe
keeps modular torsion exact, minimizes two Iwahori gluing residuals, and
rewards distance from finitely many short odd-order parabolics. The present
reported experiment instead constrains the HNN mark directly and decomposes
the full relator objective around congruence seeds. Their numerical values
must not be compared as estimates of the same quantity.

No Cairn claim uses these numerical floors. Their legitimate role is to
suggest better-controlled MSI experiments: publish the objective
normalization and code, reproduce the calibration, sweep independent seeds,
and test whether the component decomposition and seed displacement persist.
