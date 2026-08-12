# The first cuspidal harmonic planes lift through the two-adic filtration

Date: 2026-08-11

## 1. Outcome

The two certified compact cuspidal harmonic generators at every cuspidal
prime projective level below `100`, namely `p=53,61,79,89`, admit exact
corrections in
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

The residual elementary divisors can now be identified exactly.  The
two-primary correction cokernel is `C_4` at `p=53,61,89` and `C_2` at `p=79`;
both harmonic demands have zero free-cokernel component at all four levels.
Since they solve modulo eight, their two-primary component vanishes.
Consequently both harmonic generators admit corrections modulo

`2^k for every k>=1`.                                      `(HTL1a)`

This closes qualitative all-depth two-adic existence for the complete
prime-level cuspidal sample below `100`.  It is not a uniform decoder theorem:
the computed
corrections are arbitrary exact solutions, and no minimum-norm or
chart-uniform operator-norm bound follows from four levels.

The stronger full-plane norm audit is now in
`TRUE_HARMONIC_MODULAR_SECTION_PROFILE.md`.  Exhausting all `4095` nonzero
combinations modulo `64` gives worst normalized correction ratios
`0.5995627747, 0.5970593451, 0.5857626329, 0.5917473955` at
`p=53,61,79,89`, respectively.  These are constructive
upper bounds from one selected section, not claims of minimum-norm lifting.

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

The residual equation counts are diagnostics for this pivot order, not by
themselves canonical Smith invariants.  Combining their valuation profile
with the exact rational and binary ranks determines the two-local elementary
divisor in the next section.

## 4. Exact two-local cokernel and all-depth compatibility

Let `C_p=coker(A_p)` for the correction matrix at level `p`.  Exact rational
and binary ranks give:

| `p` | `rank_Q A_p` | `rank_F2 A_p` | free rank of `C_p` | `(C_p)_(2)` |
| ---: | ---: | ---: | ---: | :--- |
| 53 | 8366 | 8365 | 3086 | `C_4` |
| 61 | 11052 | 11051 | 4080 | `C_4` |
| 79 | 18458 | 18457 | 6826 | `C_2` |
| 89 | 23390 | 23389 | 8654 | `C_4` |

The free ranks are the equation counts minus the rational ranks.  The rank
drop by one modulo two shows that exactly one nonzero elementary divisor is
even.  In the direct local elimination, all rational-rank pivots are
accounted for.  At `p=53,61,89`, the unique missing pivot appears after two
divisions, so the unique even elementary divisor has two-adic valuation
exactly two.  At `p=79` it appears after one division, so the valuation is
exactly one.  This proves the last column, not merely an exponent bound.
                                                               `(HTL6)`

For each of the two harmonic demands, adjoining the demand row leaves the
rational rank unchanged:

| `p` | `rank_Q A_p` | augmented ranks for the two demands |
| ---: | ---: | :--- |
| 53 | 8366 | `8366, 8366` |
| 61 | 11052 | `11052, 11052` |
| 79 | 18458 | `18458, 18458` |
| 89 | 23390 | `23390, 23390` |

Thus their cokernel classes have zero free component.  Let `g` be either
class.  Exact solvability modulo eight says

`g in 8 C_p`.                                             `(HTL7)`

On each displayed two-primary group, multiplication by eight is zero, so
`(HTL7)` forces the two-primary component of `g` to vanish.  Multiplication
by every power of
two is an automorphism on the odd-primary torsion.  Therefore

`g in 2^k C_p for every k>=1`,                            `(HTL8)`

which is equivalent to `(HTL1a)`.  Notice that depth six is used only as an
exact certificate containing the local pivots; depth three already kills the
unique two-primary obstruction once `(HTL6)` is known.

### Normalized profiles of the selected modulus-64 section

Although the direct solutions are not norm minimizers, their normalized
basis-vector profiles are nearly identical at the two levels.  If `x_i` is
the selected correction and `c_i` the corresponding compact harmonic vector,
put

`R_(p,i)^2=(||x_i||_cent^2/n_corr)`
`          /(||c_i||_cent^2/d_compact)`.                `(HTL9)`

The common phase scale `1/64` cancels from this ratio.  Exact squared norms
give:

| `p` | basis | compact squared norm | correction squared norm | `R_(p,i)` |
| ---: | ---: | ---: | ---: | ---: |
| 53 | 0 | 109373 | 2396148 | 0.5590981882 |
| 53 | 1 | 105972 | 2284824 | 0.5546476001 |
| 61 | 0 | 148968 | 3233789 | 0.5608991744 |
| 61 | 1 | 143346 | 3243234 | 0.5726269812 |

This is rigorous flat upper-bound evidence for the two displayed basis
vectors.  It is not the minimum lift norm and not the operator norm on every
linear combination in the harmonic plane; centered reduction is nonlinear,
so neither conclusion follows from the four entries alone.

## 5. Consequence for the research program

`TRUE_HARMONIC_PRIMARY_COUPLING.md` proved only the first primary layer: the
cuspidal planes lift modulo two after restoring the omitted orientation
coordinates.  Equations `(HTL6)--(HTL8)` now show that this repair is never
destroyed by a higher binary carry at either chart.  At these levels the
remaining issue is quantitative rather than qualitative.

There are two distinct next questions.

1. **Uniform metric control.**  Even an all-depth lift need not have bounded
   normalized norm.  The TRUE theorem still requires a family-level bounded
   section compatible with the paired-discriminant metric.  The displayed
   echelon solutions do not provide that bound.
2. **Family replication.**  Construct the next cuspidal projective charts,
   compute their exact local elementary divisors, and screen the selected
   section profiles.  Flat arbitrary-section profiles suggest finite local
   templates; apparent growth must be confirmed by minimum-norm optimization
   or a dual lower bound before it counts as an obstruction.

Thus all further feasibility search on these four charts is obsolete.  The
live TRUE computation is the family-level metric problem, together with the
remaining odd-primary and universal chart-selection gates.

## 6. Reproducibility

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

The exact rank, elementary-divisor, augmented-rank, and normalized-profile
analyzer is
`experiments/sl3_projective_harmonic_primary_structure.py`.  Its committed
result artifacts are:

* `experiments/projective-harmonic-primary-p53-structure.json`, SHA-256
  `929d9827495484c4944b08c5b3b4ac19a9aa1b1d38d7932ed84a1d10a994f019`;
* `experiments/projective-harmonic-primary-p61-structure.json`, SHA-256
  `44a66205a8424d57a29b5b977283d1c0528a3d8cf2c1520495de31e7c42a6657`.
* `experiments/projective-harmonic-primary-p79-structure.json`, SHA-256
  `e6ff44aae5b814d377fad51cb143dda8453db72ad053509fb65bf986bc407ac6`;
* `experiments/projective-harmonic-primary-p89-structure.json`, SHA-256
  `abac3c4a028815006c6f36357e6599bb399be1fdf98d8e9cf1380064a6e2f4a6`.

Independent reruns of the depth-six solver reproduced the first two source
certificates exactly after deleting only the nondeterministic elapsed-time
field.  The later full-plane certificates pass the same exact modular
post-checks.  All displayed ranks were recomputed from the original integer
HAP boundaries.
