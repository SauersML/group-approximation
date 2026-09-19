---
rg: 2
id: schur-clock-router-projective-leak-proof
kind: route
title: Put a phase clock in the block commutant and read its ratios along the cyclic router
target: schur-clock-router-has-maximal-projective-leak
requires: []
---

Because every element of `D` preserves each `H_j`, every scalar block
operator belongs to `D'`.  Choose `r_j=alpha zeta^j`.  The product is

```text
product_(j=0)^(N-1) r_j
 =alpha^N zeta^(N(N-1)/2)
 =(-1)^(N-1)(-1)^(N-1)=1.
```

Therefore the cyclic equations `q_j conjugate(q_(j-1))=r_j` have a
solution: choose `q_0` arbitrarily and solve successively; the product-one
identity is exactly the closing condition.  Set `U=direct_sum_j q_j I`.

If `V_j:H_j->H_(j+1)` is the restriction of the router, then on `H_j`

```text
U V U^* V^*=q_j conjugate(q_(j-1)) I=r_j I.
```

All blocks have equal dimension, so

```text
tr_H([U,V])=(1/N) sum_j r_j
            =(alpha/N) sum_j zeta^j=0.
```

The calculation never uses the internal form of `D|_(H_j)` or of `V_j`.
Consequently it survives arbitrary character labels, irreducible
multiplicities, prescribed intertwiners, and scalar rescaling of those
intertwiners.  Those operations cannot distinguish the clock, while its
source commutators vanish and its router commutator has projective energy
one.  This proves the claim and its stated firewall scope.

