---
rg: 2
id: centralized-gram-row-vector-gap-proof
kind: route
title: Restrict a central defect Hamiltonian to each spectral representation
target: centralized-gram-row-words-upgrade-trace-gap-to-vector-gap
requires: []
---

The relations `(CGV1)` make every `q_j`, hence `D`, commute with the image of
every generator.  Since `p` is central as well, the spectral projections of
`pi(D)` and `pi(p)` commute with the entire representation.

If `(CGV4)` failed, the nonzero spectral projection

```text
e=pi(p) 1_[0,delta)(pi(D))                              (CGP1)
```

would reduce `pi`.  Restricting to `eH` gives a nonzero finite-dimensional
representation `pi_e` with `pi_e(p)=1` and

```text
tr_e(pi_e(D))<delta,                                   (CGP2)
```

contradicting `(CGV3)` applied to `pi_e`.  Hence `(CGV4)` holds.  Pairing it
with a vector and expanding `(CGV2)` gives `(CGV5)`.

Finally, if all `q_j` are the identity in a representation, every added
commutator relation is tautological.  This proves exact-completeness
neutrality and finishes the claim.
