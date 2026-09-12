---
rg: 2
id: atlas-first-disjoint-mixed-pair-authenticates-prefix-reservoir
kind: route
title: Use the first distinct-source mixed Atlas pair to authenticate the prefix reservoir
target: paired-same-reservoir-boundary-lemma
requires: []
---

**REFUTED ROUTE.** Use the first two canonical mixed rows whose root blocks
have both distinct sources and distinct targets,

```text
[x_12(e),x_43(e)]=1,       [x_12(e),x_43(f)]=1.
```

Their shared occurrence does not create a common multiplicity cut. The two
root blocks have zero products in both orders solely from their disjoint
matrix indices, leaving both fine coefficient maps arbitrary. See
`atlas-first-disjoint-mixed-pair-has-zero-reservoir-rank`.
