# The first cuspidal harmonic planes lift through the two-adic filtration

Date: 2026-08-11

## 1. Outcome

The two certified compact cuspidal harmonic generators at each of the first
two cuspidal projective levels, `p=53` and `p=61`, admit exact corrections in
the full HAP total complex modulo

`2, 4, 8, 16, 32, 64`.                                      `(HTL1)`

In particular, the earlier failure of the greedy Hensel lift at modulus
eight was not a two-adic obstruction.  It only showed that one particular
mod-two correction could not be lifted while keeping its previous residue.
Solving the full module equation modulo eight chooses a different residue
class and succeeds.

The exact sparse local-ring solve is small after unit elimination.  At
`p=53`, `8365` unit pivots reduce `11452` equations to four residual
equations; after two divisions by two, one further unit pivot clears the
residual system.  At `p=61`, `11051` unit pivots reduce `15132` equations to
two residual equations, with the same two-division pattern.  The direct
modulus-eight solves take about one second on one CPU.

This is positive evidence for the TRUE integral-repair lane, but it is not a
uniform decoder theorem.  The computed corrections are arbitrary exact
solutions and their centered Euclidean norms grow with the modulus.  Thus
`(HTL1)` proves existence through six primary layers, not a chart-uniform
operator-norm bound and not an all-depth lift.

## 2. Exact module solver

Let

`A:Z^n -> Z^m`                                             `(HTL2)`

be the selected correction boundary and let `b_1,...,b_r` be the harmonic
right-hand sides.  The problem at depth `k` is

`x_i A = b_i mod 2^k`, `1<=i<=r`.                        `(HTL3)`

The solver works directly over the local principal ideal ring
`Z/(2^k)`.  It repeatedly chooses an odd coefficient as a unit pivot and
uses invertible row operations to remove that variable from every other
equation, including equations where its coefficient is even.  Once no unit
pivot remains, every coefficient in the residual matrix is even.  Therefore

`2 A' x = b' mod 2^k`                                    `(HTL4)`

is solvable only if every coordinate of `b'` is even, and in that case it is
equivalent to

`A' x = b'/2 mod 2^(k-1)`.                               `(HTL5)`

Recursing on `(HTL5)` and then back-substituting the unit pivots proves
correctness.  The implementation shares the elimination across both
harmonic right-hand sides.  Every returned solution is independently
checked against the original integer matrix, rather than against the
eliminated system.

This avoids three unsuitable generic backends:

* field elimination, which does not apply to `Z/(2^k)`;
* mixed-integer programming, which found no feasible point in a bounded
  ten-minute modulus-eight run; and
* Boolean encodings, which expand the sparse module equation into hundreds
  of thousands of variables and more than a million clauses before using
  any local-ring structure.

The implementation is
`experiments/sl3_projective_harmonic_primary_hensel.py`.

## 3. The two exact computations

The correction variables consist of one representative from every omitted
orientation-torsion orbit in the two cellular degree-two blocks, followed by
the full `(1,1)` and `(0,2)` HAP blocks.  The exact problem sizes are:

| `p` | projective degree | full degree-two dimension | correction variables | equations |
| ---: | ---: | ---: | ---: | ---: |
| 53 | 2863 | 28630 | 22988 | 11452 |
| 61 | 3783 | 37830 | 30360 | 15132 |

For every modulus in `(HTL1)`, both harmonic right-hand sides pass exact
post-verification.  The support and centered squared norm of the selected
solutions are:

| `p` | modulus | supports | centered squared norms | direct module solve? |
| ---: | ---: | ---: | ---: | :--- |
| 53 | 2 | `3782, 3836` | `3782, 3836` | no |
| 53 | 4 | `5766, 5815` | `11718, 11752` | no |
| 53 | 8 | `6200, 5963` | `39956, 36856` | yes |
| 53 | 16 | `8072, 7994` | `244564, 249192` | no |
| 53 | 32 | `8897, 8898` | `732852, 758216` | no |
| 53 | 64 | `6917, 6760` | `2396148, 2284824` | yes |
| 61 | 2 | `5103, 5131` | `5103, 5131` | no |
| 61 | 4 | `7582, 7601` | `15019, 15011` | no |
| 61 | 8 | `8153, 8214` | `51685, 49986` | yes |
| 61 | 16 | `8851, 8799` | `205693, 204146` | yes |
| 61 | 32 | `11056, 10915` | `1299901, 1274002` | no |
| 61 | 64 | `9298, 9244` | `3233789, 3243234` | yes |

Here “no” in the last column means that ordinary greedy Hensel lifting
succeeded at that layer; it does not mean that the local-ring solver would
fail.

The large system does not fill in during direct elimination.  At modulus
eight the exact diagnostics are:

| `p` | initial nonzeros | unit pivots | elimination updates | residual equations | direct seconds |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 53 | 87226 | 8365 | 20476 | 4 | 0.7705 |
| 61 | 114982 | 11051 | 27019 | 2 | 1.0040 |

The residual equation counts are diagnostics for this pivot order, not a
canonical Smith invariant.  Their collapse nevertheless identifies the
right next exact calculation: determine the two-local elementary divisor
and Bockstein carried by this tiny residual module, rather than search the
full Boolean or integer-programming instance.

## 4. Consequence for the research program

`TRUE_HARMONIC_PRIMARY_COUPLING.md` proved only the first primary layer: the
cuspidal planes lift modulo two after restoring the omitted orientation
coordinates.  Equation `(HTL1)` now shows that this repair is not immediately
destroyed by higher binary carries.  The first possible obstruction is
therefore deeper than modulus `64` or quantitative rather than qualitative.

There are two distinct next questions.

1. **All-depth existence.**  Compute the exact two-local elementary divisor
   of the residual correction map and test the two harmonic right-hand sides
   against its integral compatibility condition.  If the residual cokernel
   has bounded two-primary exponent and the compatibility holds integrally,
   `(HTL1)` upgrades to lifts modulo every `2^k`.
2. **Uniform metric control.**  Even an all-depth lift need not have bounded
   normalized norm.  The TRUE theorem still requires a family-level bounded
   section compatible with the paired-discriminant metric.  The displayed
   echelon solutions do not provide that bound.

Thus generic feasibility search on these two charts is now obsolete.  The
live computation is the exact small residual Bockstein/elementary-divisor
calculation, followed by norm minimization only after the compatibility
class is understood.

## 5. Reproducibility

The committed result artifacts are:

* `experiments/projective-harmonic-primary-p53-sparse-direct-depth6.json`,
  SHA-256
  `ea8b688c35f4f80b5be4982ab48812411d852f550593cf587febde877e35e71f`;
* `experiments/projective-harmonic-primary-p61-sparse-direct-depth6.json`,
  SHA-256
  `4335fad84b2056cbfc72e28ee1e3a50cca12a1d23c133ef7aac1a68537674af2`.

Both were produced with one CPU using Sage 10.7.  The driver accepts the
compact cellular export, the full HAP boundary prefix, the certified
harmonic basis, and an output path, followed by `--depth 6`.  It emits the
exact post-check status and the local-ring elimination diagnostics in the
JSON artifact.
