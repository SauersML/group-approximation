---
rg: 2
id: compressed-commutant-majorana-from-wall-route
kind: route
title: Push a Clifford wall forward to the compressed commutant
target: compressed-commutant-majorana
requires: [relative-wall-commutant-growth, kun-thom-clifford-relative-wall]
artifacts:
  - notes/TRUE_RELATIVE_WALL_IS_COMMUTANT_GROWTH.md
---

The converse direction of `kun-thom-clifford-wall-normal-form-route`.  Given
a Clifford wall `C` in the original coordinates, the trace-preserving
automorphism `Ad pi(t)` carries it to `w=Ad pi(t)(C)`, which lies in
`M cap pi(t Gamma t^(-1))'` by the compressor lemma, is again a self-adjoint
involution, and satisfies the anticommutation with `Ad pi(gamma)(w)` because
`t h t^(-1)=gamma`.  Complete argument in the cited note, Theorem 3, which is
stated and proved as an equivalence.

**Why this route exists.**  Together with the forward route it encodes an
**equivalence** in the kernel's two-route form, which is the honest
representation of Theorem 3.  Recording only the forward direction made a
restatement look like a reduction with an open hole -- the trap named by the
team as "restatement dressed as reduction", which the gate cannot detect.
The pair makes the renaming visible.  Consequently the resulting cycle
between the two claims is intentional: neither can ever establish the other,
which is exactly right, since they are the same open question in two
coordinate systems.
