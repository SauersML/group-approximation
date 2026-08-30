---
rg: 2
id: kt-reduced-mf-selects-canonical-full-mf-trace
kind: route
title: Use the unique reduced trace and pull its MF coordinates back to the full algebra
target: reduced-amalgam-canonical-trace-is-mf
requires:
  - kt-double-reduced-cstar-is-mf
  - kt-q2-reduced-cstar-has-unique-trace
  - monotracial-mf-algebra-has-mf-trace
artifacts:
  - research/artifacts/kt-double-mf-trace-literature-audit-2026-08-30.md
---

Assume `C*_r(D)` is MF.  By
`kt-q2-reduced-cstar-has-unique-trace` it is monotracial, and
`monotracial-mf-algebra-has-mf-trace` therefore makes its canonical regular
trace an MF trace.

Let

```text
q:C*(D)->C*_r(D)
```

be the regular quotient.  MF traces pull back along unital star
homomorphisms: compose every coordinate map with `q`.  The pullback of the
regular trace is precisely the canonical trace on `C*(D)`, so `(RAT1)`
follows.

The converse is not used and is not known.  Trace convergence only makes
`ker(q)` invisible in normalized trace; it need not make that ideal vanish in
operator norm in the coordinate quotient.
