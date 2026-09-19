---
rg: 2
id: atlas-shifted-factorizations-have-independent-right-gauge
kind: claim
title: The thirty shifted common-U factorizations have independent right-regular gauge fibers
distinct_from:
  atlas-a4-packet-four-rectangle-normal-form: that gauges a chosen system of twelve edge messages and extracts four cycle holonomies; this shows those chosen messages are not canonical functions of the common relative unitary U.
  atlas-a4-packet-centralizer-product-compiler: that proves existence of thirty near-factorizations of one U; this identifies the exact nonuniqueness of their witnesses.
---

Use the shifted common-frame notation of
`atlas-a4-packet-centralizer-product-compiler`.  For any exact factorization

```text
U=X_j R Y_j,
X_j in rho(<a_j>)',       Y_j in rho(<b_j>)',          (A4-SHIFT-FAC)
```

and any unitary

```text
W_j in rho(A8)',
```

there is another factorization of the same `U`,

```text
U=(X_j W_j) R (W_j^-1 Y_j).                           (A4-RIGHT-GAUGE)
```

The same statement holds in the factor-reversed constraints.  The choices
`W_j` are independent for the thirty occurrences.  Thus the witness fiber
contains a copy of `U(rho(A8)')^30`.

Consequently the four rectangle holonomies of a chosen edge-message
realization are not, without an additional section or quotient, invariants of
the common relative unitary `U` itself.  A proposed common-`U` Gram identity
must either:

1. be invariant under all thirty right-gauge actions;
2. canonically fix those gauges using an additional mixed moment; or
3. be written directly in the projection-Gram coordinates of
   `atlas-common-u-second-moment-is-one-projection-gram`.

This is a non-canonicity fence, not an amplification counterexample to the
compiler.  Independent changes in `(A4-RIGHT-GAUGE)` need not correspond to a
new common `U`; they change only the existential factorization witnesses.
