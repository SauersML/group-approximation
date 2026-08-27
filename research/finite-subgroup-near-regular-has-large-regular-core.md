---
rg: 2
id: finite-subgroup-near-regular-has-large-regular-core
kind: claim
title: A finite-subgroup regular microstate is a regular core plus a vanishing remainder
distinct_from:
  near-regular-finite-character-fixes-plancherel-types: that fixes each irreducible density; this packages all finitely many densities into one largest common regular summand.
  finite-group-shared-overlap-polar-alignment: that aligns two exactifications on a common overlap; this describes one exactified finite subgroup and does not synchronize different charts.
---

Let `H` be finite and let `phi_n:H->U(d_n)` have all-pairs multiplication
defect tending to zero and normalized character tending to `delta_e` on all
of `H`.  After flexible finite-group HS exactification in dimensions
`d'_n=d_n+o(d_n)`, the resulting exact representations have decompositions

```text
sigma_n = lambda_H^(sum k_n) direct-sum r_n,
dim(r_n)/d'_n -> 0.                                    (FRC1)
```

The conclusion removes local irreducible-multiplicity freedom.  It supplies
no canonical choice of the regular summand across several finite subgroup
charts: the commutant of `lambda_H tensor 1_k` still contains the full
multiplicity unitary group.

