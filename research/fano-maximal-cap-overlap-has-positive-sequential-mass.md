---
rg: 2
id: fano-maximal-cap-overlap-has-positive-sequential-mass
kind: claim
title: Maximal Fano-cap projections have a fourfold partition sum and positive sequential profile mass
distinct_from:
  rstar-fano-caps-have-seven-maximal-parity-covers: that classifies the seven maximal caps combinatorially; this records their exact projection-sum and multi-context Hilbert--Schmidt overlap identities.
  tracial-cap-menus-are-central-core-partitions: that classifies genuine tracial branch decompositions; this positive sequential overlap is weaker and explicitly does not produce a reducing or central branch carrier.
---

**ESTABLISHED, BUT NOT A CAP SELECTOR.**  In one `R_*` context let

```text
E_lambda=sum_(t:lambda(t)=1) P_t,
lambda in F_2^3\{0}.                                   (FMO1)
```

Every nonzero assignment `t` lies in exactly four of the seven one-fibers,
so

```text
sum_(lambda != 0) E_lambda=4I.                          (FMO2)
```

For arbitrary contexts `c_1,...,c_m`, without assuming that their PVMs
commute, repeated use of `(FMO2)` and traciality gives

```text
sum_(lambda_1,...,lambda_m)
 ||E_(c_1,lambda_1)...E_(c_m,lambda_m)||_2^2=4^m.       (FMO3)
```

Hence some sequential profile has squared norm at least `(4/7)^m`.

This is positive-density information, not the missing Fano-cap model.  A
nonzero product of projections need not have nonzero common intersection or
define a reducing corner.  By `tracial-cap-menus-are-central-core-partitions`,
an exact tracial cap decomposition of one supplied model still has to come
from central profile carriers.  Thus `(FMO3)` is available as input to a new
interference/corner mechanism, but it does not establish
`culf-mastel-rstar-halt-model-has-fano-cap-support`.
