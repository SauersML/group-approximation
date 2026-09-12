---
rg: 2
id: finite-normal-certificate-hs-collapse
kind: claim
title: A finite list of approximate normal-generation identities collapses all opcode unitaries
---

Let `S={s_1,...,s_k}` be a fixed finite alphabet of formal unitary generators,
let `beta` be one fixed word in `F(S)`, and for each `s_i` fix words
`a_(i,1),...,a_(i,m_i)` and signs `eps_(i,j) in {+1,-1}`.  Define the finite
**normal-generation certificate words**

```text
r_i
 = s_i^-1
   prod_(j=1)^(m_i)
     a_(i,j) beta^(eps_(i,j)) a_(i,j)^-1.
```

Put `M=max_i m_i`.  For every matrix dimension and every unitary assignment
`V:S->U(d)`, if

```text
max_i ||r_i(V)-1||_2 <= eta,
||beta(V)-1||_2 <= delta,
```

then

```text
max_i ||V(s_i)-1||_2 <= eta + M delta.                 (NG-CERT)
```

The norm is normalized Hilbert--Schmidt.  The constant is independent of the
matrix dimension and of the lengths of the conjugator words.

This is the compiler version of normal generation: once a finite target group
has a distinguished element `b` whose normal closure contains the chosen
finite generating set, one may freeze any finite set of conjugate-product
identities expressing those generators through `b`.  An approximate model then
needs to preserve only those certificate relations and the one `b` readout.
No approximate multiplication table, approximate representation, relator
basis, irreducible decomposition, or representation-rounding theorem is
needed.
