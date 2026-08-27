---
rg: 2
id: a4-triangle-zero-traces-force-regular
kind: claim
title: Zero traces on the order-two and order-three generators force a regular A4 representation
---

Let `A,B` be finite-dimensional unitaries satisfying

```text
A^3 = 1,
B^2 = 1,
(B A)^3 = 1.
```

Assume that `A` and `B` are nontrivial in the regular-character sense

```text
tr(A)=0,
tr(B)=0,
```

for the ordinary (unnormalized) matrix trace.  Then the resulting representation
of the triangle group

```text
< a,b | a^3=b^2=(ba)^3=1 > ~= A4
```

is a direct sum of copies of `Reg(A4)`.

Equivalently, one exact mixed `(2,3,3)` triangle relation plus the two trace
conditions promotes the two marginal finite-order operators to a completely
fixed **joint** representation type.  This is useful in the atlas because the
regular `A8` character supplies the two zero-trace hypotheses automatically for
nonidentity order-two and order-three chart elements.
