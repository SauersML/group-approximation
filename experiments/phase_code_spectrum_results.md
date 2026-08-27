# Cohomological-code spectrum: a chart-selection no-go

Date: 2026-08-11

## Question

The phase-completion gate in `POPA_FACTOR_MODEL_LIFTING.md` asks for finite
charts on which small circle-cocycle defect forces small distance to the exact
cocycle locus.  A tempting computational strategy is to seek a uniform lower
bound on the first positive singular value of the finite constraint operator.

Before building the full degree-one decoder, this experiment tests a necessary
calibration: does an exact, locally free sofic chart itself force even the
degree-zero repetition code to have a repair gap?

## Two exact `F_2` chart families

On `n` points, two permutations give an exact finite action of the free group
`F_2`.  Their directed Schreier graph has `2n` generator edges.  The incidence
operator `D:C^0->C^1` is the degree-zero cocycle check; on a connected chart
its exact kernel consists of the constant functions.

The program compares:

1. two independent random permutations;
2. two random permutations acting separately inside equal halves, followed
   by one swap of images in the first permutation.

The second operation preserves bijectivity and creates exactly two directed
cross-half edges.  With probability tending to one, the random actions inside
the halves are locally free and connected.  Changing two images affects only
`O(|w|)` evaluations of any fixed word `w`, so the bottleneck sequence has the
same free local limit.  It is therefore a legitimate sofic approximation of
`F_2`, despite its macroscopic cut.

## Exact obstruction

Let `x` be the binary word which is zero on the first half and one on the
second.  In a connected bottleneck chart,

`dist_Ham(x,ker D)=1/2`,

but only the two cross-half generator checks fail, so

`|supp(Dx)|/(2n)=1/n`.

Hence the repair ratio is exactly `n/2`.  In particular, no estimate

`dist(x,ker D) <= C defect(x)^alpha`

with fixed `C` and `alpha>0` can hold on arbitrary locally free sofic charts.
This already fails for a binary phase alphabet and in degree zero.

The same word gives the spectral obstruction.  Center it to take values
`+-1`.  Its Rayleigh quotient is `O(1/n)`, hence

`sigma_min_positive(D)=O(n^(-1/2))`.

The computation identifies the sharp observed leading behavior as
approximately `2/sqrt(n)`.

## MSI results

The run used the existing Anaconda/SciPy 1.10 stack on shared node `acn116`,
restricted to four BLAS/OpenMP threads.  Sparse ARPACK diagonalization was
used; nothing was installed or run locally.

| vertices | random `sigma+` | bottleneck `sigma+` | bottleneck defect | distance | ratio |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 256 | 0.744683 | 0.127128 | 1/256 | 1/2 | 128 |
| 512 | 0.706523 | 0.089149 | 1/512 | 1/2 | 256 |
| 1024 | 0.723988 | 0.062763 | 1/1024 | 1/2 | 512 |
| 2048 | 0.739726 | 0.044284 | 1/2048 | 1/2 | 1024 |
| 4096 | 0.739869 | 0.031287 | 1/4096 | 1/2 | 2048 |

Every tested graph was connected.  The random family displays the expected
expander-like constant gap, while `sqrt(n) sigma+` for the bottleneck family
is already within about `0.2%` of `2` at `n=4096`.

## Consequence for the TRUE program

This does not obstruct the existential phase-completion statement `(PFL11)`:
that statement may choose a favorable compatible model sequence, and the
live gate is degree one with prescribed Haar/trace statistics.  It does rule
out three stronger shortcuts:

- arbitrary sofic charts need not have a uniform repair spectrum;
- essential freeness/local convergence does not prevent macroscopic code
  bottlenecks;
- a decoder theorem cannot depend only on raw local statistics of the base
  chart.

The next phase-code experiment must therefore include either an explicit
expansion/cosystolic hypothesis or the special relatively-Haar joining that
permits selection of better charts.  Computing singular values without that
extra structure will merely rediscover bottlenecks.

Artifacts: `phase_code_spectrum.py` and `phase-code-spectrum.jsonl`.
