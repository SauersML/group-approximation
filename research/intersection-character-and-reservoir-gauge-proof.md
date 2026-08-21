---
rg: 2
id: intersection-character-and-reservoir-gauge-proof
kind: route
title: Expand central idempotents at the identity coefficient and rotate regular multiplicity spaces
target: canonical-finite-packet-data-stop-at-scalar-overlaps
requires:
  - near-regular-finite-character-fixes-plancherel-types
---

Expand the two central idempotents. A product term contributes to the
canonical trace exactly when `fk=e`, so `f=k^(-1)` lies in `L=F cap K`.
Character orthogonality on `L` gives `(CFP1)`. The one-subgroup multiplicity
limits are `near-regular-finite-character-fixes-plancherel-types`, and finite
word moment convergence transfers `(CFP1)` to exactified canonical
microstates.

The Reynolds expectation is the orthogonal projection onto the finite
conjugation fixed algebra. Therefore

```text
||E_K(q)||_2^2=<q,E_K(q)>
 =|K|^(-1)sum_k tau(qkqk^(-1)),
```

proving `(CFP3)` and reducing every term to `(CFP1)`.

For sharpness, decompose a multiple of the `F`-regular representation as

```text
direct_sum_rho V_rho tensor C^(d_rho M).
```

Place the required regular `K`-action in each multiplicity space and conjugate
it by an arbitrary unitary chosen independently for every `rho`. These are
unitarily equivalent exact regular representations of `F times K`, so the
full canonical character and all scalar group-algebra moments are unchanged,
while the selected `K`-isotypic coordinates rotate independently inside the
`F` reservoirs. This proves that the scalar data do not determine ownership.
