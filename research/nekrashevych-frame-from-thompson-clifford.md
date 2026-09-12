---
rg: 2
id: nekrashevych-frame-from-thompson-clifford
kind: route
title: Free-amalgamate the non-CE source with the central-product Thompson frame
target: nekrashevych-clifford-sign-tape
requires:
  - self-similar-central-sign-cocycle
  - thompson-clifford-central-product-tape
  - non-ce-trace-on-sofic-racg
  - countable-tracial-amalgam-extension
---

Let `W_*` carry the fixed non-CE BCS trace, let `r` generate one extra copy
of `C_2`, and put

```text
Gamma_frame=(W_* * <r>) * VCl.
```

This is finitely presented.  Give it the reduced free-product trace of the
non-CE trace on `W_*`, the canonical trace on `<r>`, and the CAR crossed-
product trace on `VCl`.  Existence is the scalar-amalgam case of
`countable-tracial-amalgam-extension`.  The trace is still non-CE: the free
product von Neumann algebra has a trace-preserving conditional expectation
onto the `W_*` factor, so an embedding of the whole algebra into a tracial
matrix ultraproduct would embed the original non-CE trace.  The explicit mark
`r` is nonidentity and satisfies `tr(r)=0`.

Inside the `VCl` free factor, binary child subgroups commute, equal-depth
cylinders are conjugate by prefix replacements, the prefix swap exchanges
siblings, and `0^n10^infinity` supplies a Pauli pair at word length `O(n)`.
All these are consequences of one finite presentation by
`thompson-clifford-central-product-tape`.  The free product with `W_*` imposes
no cross-context commutation on the source selectors.  Thus the source trace
extends, the frame transports one relative CAR qubit per level, and all five
interfaces of the target hold.  Coupling source predicates to those cells is
deliberately left to the separate violation-density recurrence.
