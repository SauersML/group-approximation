# Cross-pair parity already grows in the first two projective charts

Date: 2026-08-11

## Outcome

The uniform matching decoder on the ordinary singleton line does not extend
to a bounded one-row formula for demands between distinct matching orbits.
For the first such fixed demand tested in the full mod-two HAP boundary,

`x d_3=e_1+e_7`,                                                `(PQC1)`

the exact minimum source support is

`11` at `p=3`,                                                   `(PQC2)`

whereas at `p=5` every source of support at most `13` is impossible:

`minimum support >=14`.                                         `(PQC3)`

The latter instance has a verified Gaussian-elimination filling of support
`61`, so its exact minimum lies in `[14,61]`.  This is the first certified
finite-level growth for a cross-pair coset leader in the full degree-three
boundary.  It is consistent with the logarithmic global no-go in
`TRUE_BOUNDED_DEGREE_PARITY_DECODER_NO_GO.md`, but two levels do not prove
divergence for this fixed demand.

The immediate strategic consequence is negative but useful: do not try to
extend the matching theorem by lifting its `p=3` source pattern verbatim.
That eleven-row pattern has boundary weight `60,70,70` at `p=5,7,11`,
respectively, rather than the required two-coordinate demand.  Its
cancellations are level-specific.  A viable family theorem must use the
restricted harmonic/carry input lattice, a new projective formula, or the
nonlinear paired-discriminant geometry.

## Exact finite problem

Let

`D_p:F_2^(20N_p)->F_2^(10N_p)`, `N_p=p^2+p+1`,                  `(PQC4)`

be the total specialized HAP boundary in degree three.  Coordinates `1` and
`7` are ordinary singleton targets in different orbits of the involution
used by `TRUE_PROJECTIVE_SINGLETON_MATCHING_DECODER.md`.  We solve

`min {|supp(x)|:x D_p=e_1+e_7}`.                                `(PQC5)`

The SAT encoding keeps one Boolean variable for each source coordinate,
adds each boundary coordinate as a native XOR clause, and adds a sequential
cardinality constraint `sum x_i<=k`.  A SAT answer is checked independently
by multiplying the selected source rows over `F_2`.  An UNSAT answer at
bound `k` rules out every smaller bound by monotonicity.

At `p=3`, bounds `0,...,10` are UNSAT and bound `11` is SAT.  The verified
optimal source is

`{77,101,103,108,111,138,144,151,157,219,245}`.                 `(PQC6)`

At `p=5`, bounds `11,12,13` are UNSAT.  Checking bound `11` already excludes
all smaller supports, so `(PQC3)` follows without solving fourteen separate
instances.  We deliberately did not spend more time on bound `14`: the
finite growth signal, rather than the exact second optimum, is the useful
result.

## Reproducible certificates

The solver and independent verifier are:

* `experiments/sl3_projective_parity_cms.py`;
* `experiments/sl3_projective_parity_milp.py`.

The committed solver records are:

* `experiments/projective-parity-cross-p3-cms.json`;
* `experiments/projective-parity-cross-p5-cms.json`.

They use CryptoMiniSat `5.14.7` through native XOR clauses and the sequential
cardinality encoder in python-sat `1.9.dev13`.  The exported boundary hashes
are stored in the records.  Both returned fillings were checked against the
input boundary after solving; the `p=3` record is an exact optimum and the
`p=5` record is an exact lower bound plus a verified feasible upper bound.

## Relation to the sparse Bernoulli route

This computation measures a coset-leader weight, not the Bernoulli
carry/witness incidence ratio from `FALSE_BERNOULLI_CARRY_INCIDENCE.md`.
Growth of `(PQC5)` is therefore not a FALSE certificate.  It does identify
the same structural resource needed by that route: sparse local equations
whose marked syndrome becomes increasingly nonlocal.

The next high-yield calculation should not blindly continue `p=7`.  It
should first quotient by the exact matching-difference summand and express
the surviving pair-orbit boundary symbolically.  That reduced matrix can
then serve both purposes:

1. test whether the actual harmonic/carry demands avoid the growing coset
   leaders required by the full no-go;
2. measure carry-row and marked-witness incidence on candidate binary
   subcodes for the Bernoulli FALSE criterion.

This is a smaller and more theorem-shaped search than optimizing the full
`20N_p`-variable system at more primes.
