---
rg: 2
id: degree-four-kl-inner-retractions-fail-proof
kind: route
title: Reject every cycle and coordinate-packet inner image on an exact moved vector
target: degree-four-kl-inner-retractions-fail
requires:
  - degree-four-kl-source-face-retraction
---

Use the four relators `(DG2)` in
`degree-four-kl-source-face-retraction-proof`.  A candidate retraction fixes
`G_0`.  For each `i=1,2,3`, choose

```text
phi_i=1,  phi_i=Ad(p^k),  or
phi_i=Ad(p^k q p^(-k)),       0 <= k < 20.             (IR1)
```

There are `41^3=68921` triples.  The equation `R0=1` is linear in its final
`z`, so it uniquely sets

```text
z=(r0 e1 a2 c1 b3 d2 p3)^(-1).                       (IR2)
```

The artifact substitutes `(IR2)` into `R1,R2,R3`.  It acts each resulting
word on the faithful standard module whose basis is a matrix coordinate and
an infinite binary word.  For a tested vector the script retains an opaque
tail and exposes at least as many initial bits as the total number of deletion
operators in the word.  Therefore a moved vector is a literal witness in the
infinite module, not evidence from a truncation.  Four deterministic prefix
patterns and all twenty matrix coordinates suffice to find a witness in every
case.

The run was performed remotely through the permitted MSI wrapper:

```text
/Users/user/msi-node/msi put \
  research/artifacts/screen-degree4-full-copy-inner.py \
  /projects/standard/hsiehph/sauer354/screen-degree4-full-copy-inner.py
/Users/user/msi-node/msi \
  'python3 /projects/standard/hsiehph/sauer354/screen-degree4-full-copy-inner.py'
```

The exact output was

```text
cases=68921
rejected_by_R1_R2_R3=(68921, 0, 0)
witness_screen_survivors=0
```

The phrase `witness_screen` limits the positive direction only: a survivor
would require a complete identity audit.  Since every case has an explicit
moved vector, the zero-survivor conclusion for the family `(IR1)` is exact.
