---
rg: 2
id: two-step-fold-loop-64-proof
kind: route
title: Evaluate the shared fold return as a mixed second difference
target: two-step-fold-loop-has-finite-64-model
requires: []
---

The additive group of `B` has the four-element basis

```text
1,e,h,eh,
```

so it has order `16`.  Multiplication by `1+e` and by `1+h` gives commuting
linear automorphisms, and

```text
(1+e)^2=(1+h)^2=1.                                    (1)
```

They therefore define the indicated action of `C_2 times C_2`; hence `G`
is a finite group of order `64`.  Write `c(b)` for the element of its normal
additive subgroup corresponding to `b in B`.  With commutator convention
`[x,y]=xyx^(-1)y^(-1)`, conjugation by the actors gives

```text
[c(b),S]=c(hb),              [T,c(b)]=c(eb).           (2)
```

It follows directly that

```text
[T,[c(b),S]]=c(ehb).                                  (3)
```

The additive subgroup has exponent two and is abelian.  Therefore the
assignments `(TSF6)` give

```text
C_0C_1=c(1+h)=J.                                      (4)
```

Substitute `b=1,h,1+h` in `(3)`.  Since `h^2=0`, this yields

```text
D_0=c(eh)=M,
D_1=c(eh^2)=1,
D=c(eh(1+h))=c(eh)=M.                                (5)
```

The basis vector `eh` is nonzero in `B`, so `M` is a nonidentity involution.
In the left regular representation, `lambda(M)` has a `-1` eigenvector
(subtract the two basis vectors in any two-cycle of left multiplication by
`M`).  Thus `(TSF7)` follows.  Every occurrence of `S` and `T` in `(5)` is
the same semidirect-product actor, while `(1)` gives `(TSF3)` exactly.

