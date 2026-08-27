---
rg: 2
id: fp-cayley-expander-occurrence-edge-proof
kind: route
title: Convert a quasi-isometric expander embedding into finitely many edge offsets
target: fp-cayley-expanders-give-bounded-occurrence-edges
requires: []
---

Use the Sapir--Osajda finitely presented group `A` and fix a finite generating
set.  If the embedded expander family has uniform quasi-isometry constants
`L,C`, then adjacent vertices satisfy

```text
d_A(i_n(u),i_n(v)) <= L+C.                                      (1)
```

Let `D` be the finite word ball of radius `ceil(L+C)`.  Equation `(1)` gives
`(FCE2)`.

For an edge with `i_n(v)=i_n(u)d`, direct substitution gives

```text
A_(n,v)=i_n(u) (d a d^-1) i_n(u)^-1.                            (2)
```

Therefore every word comparing `A_(n,u)` and `A_(n,v)` is the conjugate by
`i_n(u)` of the corresponding root word for `d`.  Normalized Hilbert--Schmidt
norm is invariant under conjugation, so its defect is exactly the prototype
defect and is independent of the address length and of `n`.

