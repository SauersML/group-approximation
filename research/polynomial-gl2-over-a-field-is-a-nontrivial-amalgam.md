---
rg: 2
id: polynomial-gl2-over-a-field-is-a-nontrivial-amalgam
kind: claim
title: GL_2 of a one-variable polynomial ring over a field is a nontrivial amalgam of GL_2 of the field with the polynomial Borel subgroup (Nagao)
---

**ESTABLISHED.** (Nagao.) Let `k` be a field and `B` the upper-triangular subgroup of `GL_2`. Then

```text
GL_2(k[t]) = GL_2(k) *_(B(k)) B(k[t]).
```

The amalgam is nontrivial, since `B(k) ≠ GL_2(k)` and `B(k) ≠ B(k[t])`. So `GL_2(k[t])` acts without inversions on
the Bass–Serre tree. That tree has vertex set `GL_2(k[t])/GL_2(k) ⊔ GL_2(k[t])/B(k[t])`, and its vertex stabilizers
are the conjugates of `GL_2(k)` and of `B(k[t])` (Serre, *Trees*, I.4.1).
