---
rg: 2
id: finite-sign-safe-base-has-bounded-pauli-capacity
kind: claim
title: A fixed finite sign-safe base has bounded Pauli capacity
distinct_from:
  relative-coset-pauli-incidence-compiler: that allows an infinite finitely presented address group with unbounded coset spaces; this audits the proposal to absorb all rectangles into one fixed finite base group.
  sign-double-cosets-separate-pauli-clouds: that derives injectivity from a nondegenerate sign table; this observes that a finite base then permits only finitely many such rows and columns.
---

Let `B` be finite, let `H_X,H_Z<=B`, and let the two Pauli signs be unions of
disjoint double cosets in `H_X\B/H_Z`.  The induced binary sign matrix

```text
M_B : B/H_X  x  B/H_Z -> F_2                                  (FSB1)
```

has at most `[B:H_X]` rows and `[B:H_Z]` columns and therefore fixed rank

```text
rank_F2(M_B) <= min([B:H_X],[B:H_Z]).                           (FSB2)
```

The associated coset-Clifford algebra consequently has a representation of
dimension at most

```text
2^rank(M_B),                                                    (FSB3)
```

a constant depending only on `B`.

Hence one finite sign-safe base can absorb every **bounded local rectangle
type**, but it cannot by itself carry a robust Pauli dimension witness
`D_N->infinity`.  Any terminal base-packet construction must add a global
coordinate whose sign profiles have unbounded binary rank; merely taking
more occurrences of the same finite coset types permits packet reuse.
