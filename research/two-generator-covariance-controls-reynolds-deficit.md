---
rg: 2
id: two-generator-covariance-controls-reynolds-deficit
kind: claim
title: Two named covariance defects are bounded by eight times the finite-group Reynolds deficit
distinct_from:
  raw-swap-forces-two-s3-covariance-energy: that supplies a positive lower bound for two specific raw S3 defects; this is the general Hilbert-space inequality converting any two such defects into distance from the whole subgroup commutant
---

Let `K` be a finite group, let

```text
rho : K -> U(d)
```

be any unitary representation, and let `E_K` be the normalized conjugation
average, hence the normalized-Hilbert--Schmidt orthogonal projection onto the
commutant `rho(K)'`.  For any unitary `U` and any two elements `a,b in K`, put

```text
A = ||U rho(a) U^* - rho(a)||_2,
B = ||U rho(b) U^* - rho(b)||_2.
```

Then

```text
A^2+B^2 <= 8 ||U-E_K(U)||_2^2
          = 8 (1-||E_K(U)||_2^2).                     (TCR)
```

No representation-theoretic spectral gap is needed.  The estimate is uniform
in `d`, in the multiplicity of `rho`, and in the choice of the two group
elements.
