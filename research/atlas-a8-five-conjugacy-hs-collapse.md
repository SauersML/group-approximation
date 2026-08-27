---
rg: 2
id: atlas-a8-five-conjugacy-hs-collapse
kind: claim
title: Five approximate conjugacy identities plus collision 19243 collapse all six standard A8 transvection opcodes
artifacts:
  - experiments/atlas_a8_transvection_normal_certificates.py
---

Let

```text
T01,T10,T12,T21,T23,T32 in U(d)
```

be arbitrary unitaries.  Evaluate the five frozen nontrivial certificate words
`r_s` from `atlas-a8-six-transvection-normal-certificates` by substituting these
six matrices for the corresponding standard transvection letters.  If

```text
max_(s != t23)||r_s(T)-1||_2 <= eta,
||T23-1||_2 <= delta,
```

then

```text
max{||T01-1||_2,||T10-1||_2,||T12-1||_2,
    ||T21-1||_2,||T23-1||_2,||T32-1||_2}
 <= eta+delta.                                           (A8-5CHECK)
```

The estimate is dimension-free and does **not** charge the conjugator lengths
`8,10,4,6,2`: every certificate contains exactly one conjugate of `T23`, and
unitary conjugation is an isometry for normalized Hilbert--Schmidt distance.
Thus the 19243 compiler has an exact constant-one propagation layer once the
five relation loops have been extracted.
