---
rg: 2
id: central-sign-reynolds-canonical-density-proof
kind: route
title: Read the identity coefficient of the central-sign assignment atom
target: central-sign-reynolds-atoms-have-fixed-canonical-density
requires:
  - central-sign-bcs-atoms-are-subgroup-reynolds-projections
artifacts:
  - notes/NONHYPERLINEAR_FINITE_MEMORY_REYNOLDS_AUDIT.md
---

The subgroup `H_a` has order `2^k`, does not contain `J`, and
`<H_a,J>=C`.  Expanding the two commuting factors gives

```text
A_a
 =2^(-(k+1)) sum_(h in H_a) (h-hJ).                    (CDP1)
```

Because the context packet embeds, the identity occurs exactly once in
`(CDP1)`, namely as the term `h=1` in the first sum.  No term `hJ` is the
identity because `J notin H_a`.  The canonical group trace reads the identity
coefficient, proving `(CSD1)`.

The atom is a fixed finite group-algebra polynomial and a projection.
Canonical hyperlinear microstates converge in trace on that polynomial.
Flexible exactification changes its value by `o(1)`, proving `(CSD2)`.

