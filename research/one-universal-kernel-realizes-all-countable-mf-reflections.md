---
rg: 2
id: one-universal-kernel-realizes-all-countable-mf-reflections
kind: claim
title: One perfect singly normally generated kernel realizes every countably infinite MF reflection
artifacts:
  - non_mf_groups_exist.tex
  - notes/MF_REFLECTION_AND_CORONA_SUPPORT_CALCULUS.md
---

Assume `B` is finitely generated, `B!=D=<d>`, `B` is perfect with full MF
radical, and `d` normally generates `B`.  For a nonempty set `I`, put

```text
K_I=*_(D,i in I) B_i.
```

Then:

```text
Rad_MF(K_I)=K_I,
[K_I,K_I]=K_I,
normalClosure_(K_I)(d)=K_I.                          (UK1)
```

The group `K_I` is finitely generated exactly when `I` is finite.  Its
isomorphism type depends only on the cardinality of `I`.

Consequently there is one fixed countable group

```text
K_infinity=*_(D,n in N) B_n                          (UK2)
```

which is perfect, not finitely generated, singly normally generated, and has
full MF radical, such that every countably infinite group `Q` admits a
left-regular action on `K_infinity` with

```text
C_d(Q) ~= K_infinity semidirectProduct Q.             (UK3)
```

If `Q` is MF, the kernel `K_infinity` in `(UK3)` is exactly the MF radical
and the quotient is the universal MF reflection.  If `Q` is finitely
generated, then `C_d(Q)` is finitely generated even though its exact hidden
kernel is not.  In particular, one finitely generated group with quotient
`Z` has a perfect, infinitely generated, singly normally generated exact MF
radical, and one relation changes it to an MF group.

