---
rg: 2
id: global-tracial-positivity-cannot-separate-group-trace-proof
kind: route
title: Evaluate the purported universal certificate in the group von Neumann algebra
target: global-tracial-positivity-cannot-separate-group-trace
requires: []
artifacts:
  - research/artifacts/nonhyperlinear-random-presentation-and-matricial-separator-2026-08-18.md
---

The left regular unitaries `lambda(s)` live in the tracial von Neumann algebra
`L(Gamma)` and satisfy every group relator exactly.  Therefore any implication
that is sound in every tracial von Neumann algebra satisfying those relators
must hold after the substitution `s -> lambda(s)`.  If it concluded `P>=0`,
positivity of the canonical trace would give

```text
tau_Gamma(P(lambda(S))) >= 0,
```

contrary to the assumed negative canonical value.  Hence a successful
finite-matrix separator must use a genuinely matricial-only inequality rather
than universal tracial positivity.
