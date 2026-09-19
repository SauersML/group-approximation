# Two-chart atlas search: first MSI signal

Date: 2026-08-10

## Question tested

`notes/EXPLICIT_LEAVITT_ATLAS.md` reduces hyperlinearity of the explicit
nonsofic binary-Leavitt group to a relative-unitary problem for two copies
of `A8`.  Its full finite normal-generating list for the atlas kernel has
not yet been extracted, so the exact endpoint optimization cannot yet be
run.

The experiment `atlas_two_chart_search.py` tests an explicit necessary
subsystem.  It translates the following identities through the two concrete
leaf charts:

- Steinberg commutator identities with one scalar coefficient;
- `e*e = f*f = 1`, `e*f = f*e = 0`, and `ee* + ff* = 1`;
- a representative family of commuting-root commutators.

After exact free-product reduction there are 54 distinct relation words
`r` in the kernel `R`.  For each `r`, the experiment uses six elementary
generators `p` of each `A8 = GL_4(F_2)` factor.  This gives 648 explicit
constraints `[p,r]` in `[P,R]`.

Each chart acts faithfully on the 15 nonzero vectors of `F_2^4`.  At
multiplicity `k`, the only variable is the relative unitary

`U in U(15 k)`.

The tested loss of a constraint word `w` is its normalized Hilbert--Schmidt
defect `||pi_U(w)-1||_2`.  The first objective minimizes the RMS of all 648
defects.  The second repeatedly optimizes the currently worst 32 constraints
as a nonsmooth max-loss heuristic.

This is a necessary subsystem only.  Vanishing loss here would not prove
hyperlinearity until a full normal-generating list is extracted.  Conversely,
a proved dimension-free positive lower bound for even this subsystem would
rule out this particular atlas construction.

## Validation

All execution was on MSI `acn116`, restricted to four cores with
`OPENBLAS_NUM_THREADS=4`, `OMP_NUM_THREADS=4`, and `taskset -c 0-3`.
Nothing was built or executed locally.

The analytic cyclic gradient was checked against centered finite differences
at steps `1e-3`, `3e-4`, and `1e-4`.  The absolute discrepancies were

`8.79e-7`, `7.91e-8`, and `8.79e-9`,

respectively.  Exact amplification also reproduces a lower-multiplicity
score to floating-point precision, which prevents larger dimensions from
looking worse merely because of a random restart.

Problem construction also evaluates every one of the 54 source words using
exact `F_2` Leavitt monomial arithmetic.  Each word must reduce to the unit
before its 12 centrality commutators are admitted to the optimizer.  The
complete 54-word validation passed on MSI.

## Results

Mean-loss optimization:

| multiplicity `k` | dimension | best RMS defect | max defect at that point |
| ---: | ---: | ---: | ---: |
| 1 | 15 | 0.6769395892 | 1.3174374522 |
| 2 | 30 | 0.6349441013 | 1.3474010904 |
| 4 | 60 | at most 0.6349441013 by exact amplification | not separately optimized |

Worst-tail optimization:

| multiplicity `k` | dimension | best max defect | RMS defect at that point |
| ---: | ---: | ---: | ---: |
| 1 | 15 | 1.2725605209 | 0.9384031255 |
| 2 | 30 | 1.2495774681 | 0.7742400855 |
| 4 | 60 | 1.2390789534 | 0.8433237019 |

The `k=2` RMS improvement over `k=1` and the monotone max-defect improvement
`1.27256 -> 1.24958 -> 1.23908` are genuine multiplicity gains: every larger
run was seeded by exact amplification of a smaller optimizer.  They show that
nonclassical multiplicity directions exist.  The gain is slow, however, and
no tested model is remotely close to making every relation central.

The active worst constraints move during optimization, but the persistent
families are the scalar Steinberg relations and the `e*e`, `f*f`, and
partition-of-one relations.  They are better candidates for a
dimension-free trace/SOS inequality than the older global-coboundary
experiment, whose exact stratum is already analytically sterile.

## Exhaustive classical-alignment audit

An exact finite scan rules out the simplest explanation for the numerical
floor.  For a relative automorphism `phi` of `A8`, map the first chart
identically to `A8` and the second by `phi`, then evaluate all 54 source
relations exactly.

- Among all 20,160 inner automorphisms, the best two alignments satisfy
  exactly 42 of 54 relations.  One fails a 12-relation `e` branch and the
  other fails the corresponding `f` branch.
- Among all 20,160 automorphisms in the outer coset of
  `Aut(A8) = S8`, the best two satisfy only 20 of 54 relations.
- Therefore no automorphism of `A8` makes the necessary subsystem exact.

The inner scan used exact `GL_4(F_2)` matrices.  The outer scan used GAP's
isomorphism from the faithful 15-point `GL_4(F_2)` action to `A8`, followed
by conjugation by an odd permutation and every inner conjugation.  Thus all
40,320 automorphisms were covered.  This closes only the same-target
classical alignment sector; it does not rule out larger finite targets or
nonclassical unitary mixing.

## Artifacts and next step

- `atlas_two_chart_search.py`: exact `F_2` word construction and optimizer.
- `atlas_inner_scan.py` and `atlas-inner-scan.json`: exhaustive inner scan.
- `atlas_outer_scan_export.py` and `atlas-outer-scan.txt`: exhaustive outer
  automorphism-coset scan through GAP.
- `run_atlas_search.sbatch`: one four-core bounded reproduction job.
- `atlas-k{1,2,4}-focus.npy`: best max-focused relative unitaries.
- `atlas-search-refined.log` and `atlas-search-focus.log`: complete JSON-line
  records of the reported runs.

The next high-value task is not a larger blind run.  It is to extract a
finite normal-generating list for the two-chart kernel, or at least enlarge
the necessary subsystem with a mechanically complete finite Steinberg
presentation.  Only then can dimension scaling distinguish a constructive
hyperlinear model from optimization freedom specific to the current subset.
