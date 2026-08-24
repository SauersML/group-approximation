---
rg: 2
id: finite-pvm-couplings-with-approximate-inverses-classicalize
kind: claim
title: Approximately multiplicative finite PVM couplings with stochastic inverses classicalize to permutations
distinct_from:
  finite-cylinder-mixed-traces-kill-normalizer-holonomy: that starts with exact unitary covariance of a finite group action and removes stabilizer multiplicity representations; this starts with classical block-mass couplings and uses approximate inverses to make them deterministic.
  diagonal-normalizer-rigidity: that assumes a unitary normalizes a full diagonal algebra; this needs only the finite matrices of squared block masses and no operator normalizer.
---

Fix `m` and `c>0`.  Let `mu=(mu_1,...,mu_m)` be a probability vector with
every nonzero entry at least `c`.  A self-coupling `C` of `mu` is a
nonnegative `m x m` matrix whose row and column sums are `mu`.  Give such
matrices total-variation norm.

For every finite symmetric multiplication window `F` and every sufficiently
small `epsilon`, suppose self-couplings `(C_g)_(g in F)` satisfy

```text
||C_e-Diag(mu)||_TV <=epsilon,
||C_(gh)-C_g o_mu C_h||_TV <=epsilon                  (FPC1)
```

whenever the displayed product is tested, where

```text
(C o_mu D)_(i,k)=sum_(j:mu_j>0) C_(i,j)D_(j,k)/mu_j. (FPC2)
```

Assume the window contains inverses and the products `gg^(-1)`.  Then there
is a modulus `f_(m,c)(epsilon)->0` and `mu`-preserving permutations
`sigma_g` of the atom set such that

```text
||C_g-C_(sigma_g)||_TV <=f_(m,c)(epsilon),             (FPC3)
```

and the permutations are `f_(m,c)(epsilon)`-multiplicative on the tested
window (after discarding atoms of total `o(1)` weight if `mu` itself varies
by `o(1)`).  Rationally splitting the atom weights and taking a common
multiple realizes the same conclusion by ordinary permutations of a finite
set, with normalized Hamming error tending to zero.

Thus a finite PVM whose unitary block-mass couplings obey `(FPC1)` already
provides the classical finite-state part of a sofic-action chart.  No
monomialization of the original unitaries is required.

