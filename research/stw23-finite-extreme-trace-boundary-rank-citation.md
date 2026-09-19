---
rg: 2
id: stw23-finite-extreme-trace-boundary-rank-citation
kind: route
title: Apply Tikuisis--Toms rank surjectivity and Haagerup trace linearity
target: stw23-finite-extreme-trace-boundary-has-all-ranks
requires: []
artifacts:
  - research/artifacts/stw18-23-26-finite-tracial-boundary-audit-2026-08-30.md
---

Tikuisis--Toms, *On the structure of the Cuntz semigroup in (possibly)
nonunital C-star-algebras*, Canadian Mathematical Bulletin 58 (2015), no. 2,
Corollary 4.4, prove that for a unital simple C-star algebra with finite
nonempty extreme tracial boundary the rank map

```text
(A tensor K)_+ -> LAff(T(A),(0,infinity]),
a |-> (tau |-> d_tau(a))
```

is onto.  Their finite-boundary construction does not use strict
comparison.  Since the `A` in the target claim is exact, Haagerup's theorem
says that every bounded quasitrace on `A` is a trace.  Hence `QT(A)=T(A)`,
and the cited surjectivity is exactly the asserted quasitracial rank
realization.
