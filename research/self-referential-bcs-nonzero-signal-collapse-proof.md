---
rg: 2
id: self-referential-bcs-nonzero-signal-collapse-proof
kind: route
title: Search for a proof that the machine's own distinguished BCS signal vanishes
target: self-referential-bcs-nonzero-signal-collapse
requires:
  - fanizza-et-al-computable-bcs-signal-family
---

Take `L` to be the RE set of indices of machines which halt on empty input,
and fix the computable `L`-family `(B_m,C_m)` from `(FBS1)--(FBS2)`.

Equality to zero in a finitely presented rational star-algebra is recursively
enumerable: enumerate finite rational linear combinations of two-sided
star-multiples of the defining relators and compare their expanded
noncommutative polynomials with the target. Therefore, uniformly in `m`, a
machine can enumerate formal certificates that

```text
D_m=(1-x_(D,m))/2=0 in A(B_m).                                  (SBS3)
```

By Kleene's recursion theorem choose a machine `M_*` with index `m_*` which
computes `B_(m_*)` and halts exactly when this enumeration finds `(SBS3)`.

If `M_*` halted, then `m_* in L`. By `(FBS1)` there would be a tracial state
`tau` on `A(B_(m_*))` with `tau(D_(m_*))>0`. But the certificate found by the
machine proves `D_(m_*)=0`, a contradiction. Hence `M_*` does not halt.

The enumeration is complete for ideal membership, so its failure to halt
implies `D_(m_*)!=0`, proving `(SBS1)`. Since `m_* notin L`, `(FBS2)` applies
with the computable integer `C_(m_*)` and proves `(SBS2)`.
