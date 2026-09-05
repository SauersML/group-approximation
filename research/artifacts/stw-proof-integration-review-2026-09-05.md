# Review and integration of the September 5 proof batch

This records internal mathematical review and Cairn graph validation.
Neither is external peer review or formal proof verification. The named
problem count remains one internally reviewed solution manuscript, STW
LIX; LVIII, LXI, and LXXVI remain open.

## Reviewed results

- The exact factorial component-group proof identifies the entire
  finite-stage gauge component group by the section fibration and its
  integral Euler image. Generator transport and finite-stage detection
  identify the component group of the simple AH limit.
- The arbitrary-cyclic refinement replaces the initial sphere by
  `S^2 x CP^(d-1)`. Its Euler image is exactly `d Z`, not just a subgroup
  of it: all coefficients are multiples of `d`, and `kappa L_0`
  attains `+d` or `-d`. Boundary naturality gives the initial generator.
  The signed product-zero calculation transports it by multiplication
  by `+1` or `-1` at every stage. Thus the entire limit group is `Z/d`.
- The finite-representation commutator proof forces the tautological
  overlap function to attain both endpoints and therefore its midpoint.
  The MF extension retains every coordinate in its block sums, so the
  quotient map stays isometric; polar repair lifts each individual
  quotient unitary. The norm-one obstruction survives the limsup.
  Properly infinite coefficient algebras are outside that hypothesis.
- The exact strict relative positive-embedding proof controls weighted
  spectral tails uniformly and applies finite-dimensional selection only
  to strict embedding fibers and prescribed boundary singletons.
  The full comparison proof closes the cutoff equality locus before
  constructing its projection boundary data. Sequential Cu continuity
  then removes the base dimension bound. This proves order reflection,
  not arbitrary target realization.
- The finite projection-patch reduction preserves a target hereditary
  sandwich. The two-patch decompositions use actual orthogonal module
  splittings and retain the angle remainder. Vanishing scalar weights
  do not require bounded inverses at the support boundary. The soft and
  uniform-angle-gap cases give exact lifts; arbitrary remainders remain
  unproved.

## Native graph checks

The prior batch was validated on MSI with the native commands
`/usr/bin/python3.11 tools/cairn.py check --changed` and
`/usr/bin/python3.11 tools/cairn.py preview`. Both passed on the relevant
57-node closure (30 claims and 27 routes). The four new claims derived
as established; LIX remained refuted and LVIII, LXI, LXXVI remained open.

The checked batch was committed and pushed as `47e34ed2f`.
Logs are on shared storage under
`/projects/standard/hsiehph/sauer354/stw79-cairn-check-20260904/cu-all-base-scope-20260905/`:
`proof-batch-check.log` and `proof-batch-preview.log`.
Later integrations rerun these commands and replace those log files;
their final counts are recorded below when complete.

The arbitrary-cyclic and MF refinements subsequently passed both native
commands on the enlarged 61-node closure (32 claims and 29 routes).
Both new claims derived as established. The named root statuses were
unchanged. The two projection-patch artifacts are linked as partial
results and do not supply a route closing LXXVI.

Cairn checks route dependencies, schema, and derived graph status. They
do not establish the mathematical validity of a manuscript. The scope
is the relevant dependency closure, not every concurrently changing
file in the repository. No local code execution or builds were used.
