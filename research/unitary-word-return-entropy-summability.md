---
rg: 2
id: unitary-word-return-entropy-summability
kind: claim
title: Random word return is summably dominated by representation-stratum entropy
artifacts:
  - research/artifacts/nonhyperlinear-random-presentation-and-matricial-separator-2026-08-18.md
---

There are finite parameters `k,R,L,m`, constants `delta,eps,eta>0`, and a
finite distribution `mu_L` on length-`L` cyclically reduced relators for
which:

1. with positive probability, `m` independent relators preserve all distinct
   words in the free ball `B_R` (for example through a suitable
   small-cancellation event `SC`);
2. for every matrix size `n`, the `delta`-separated unitary tuples admit an
   `eta`-net `N_n` such that, with

   ```text
   p_n(U)=Pr_(r~mu_L)[d_2(r(U),1)<=2 eps],
   ```

   one has the summable entropy/return inequality

   ```text
   sum_n sum_(U in N_n) p_n(U)^m < Pr(SC).
   ```

The intended theorem is **not** a uniform `exp(-c n^2)` return bound.  That
statement is false on scalar tuples and on fixed matrix blocks repeated with
growing multiplicity.  The proposed bound instead matches return probability
to the metric entropy of the tuple's simultaneous-conjugacy / generated
matrix-algebra stratum.  Repeated-block tuples have low quotient-moduli entropy,
while genuinely irreducible high-complexity strata are expected to have
`n^2`-scale anti-concentration.

## Attempts

- **Generic word-map volume.**  Avni--Glazer--Larsen's dimension-uniform
  small-ball estimates for fixed nontrivial word maps on `SU_n` control the
  Haar average of the random-relator return function by Fubini.  Convert the
  measure of high-return loci into packing bounds using a radius gap and the
  `L`-Lipschitz word-evaluation estimate.  The missing step is a sharp quotient
  packing argument on simultaneous-conjugacy classes.
- **High return -> structure.**  Use noncommutative
  Balog--Szemeredi--Gowers/inverse theory: anomalously large random-walk return
  should force a controlled approximate subgroup.  Breuillard--Green's
  unitary approximate-group theorem then pushes the tuple toward an
  almost-abelian stratum.  What is needed is a quantitative version whose
  dimension dependence is paid for by the entropy drop of that stratum.
- **Abelian/repeated-block base cases.**  After diagonalization, random reduced
  words become a lattice random walk in the exponent-sum vector evaluated on
  joint eigenphases.  Prove toral Littlewood--Offord/local-CLT bounds in terms
  of the number of phase parameters, not ambient matrix size, and extend by
  finite direct sums of bounded-size blocks.
- **Falsification experiment.**  In small dimensions, bin tuples by approximate
  commutant dimension and block type, estimate word-return probabilities, and
  compare `-log p` with local quotient-moduli entropy.  A family with both high
  return and genuinely large quotient entropy would directly refute the
  proposed stratification mechanism.
