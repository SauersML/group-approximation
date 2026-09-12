---
rg: 2
id: one-root-p3-regular-leak-proof
kind: route
title: Put the centralizer on the root generator in separating finite BS quotients
target: one-root-p3-denominator-fragment-has-finite-regular-leaks
requires: []
---

Use the normal form

```text
BS(1,n)=Z[1/n] rtimes_n Z.
```

It is residually finite by an elementary two-case argument.  An element
`(r,k)` with `k!=0` survives after killing `Z[1/n]` and reducing the second
coordinate modulo any integer not dividing `k`.  If `k=0` and
`r=m/n^s!=0`, choose a prime `q` dividing neither `mn`; reduction of
`Z[1/n]` modulo `q`, together with reduction of the second coordinate
modulo `ord_q(n)`, gives the finite affine quotient in which `r` survives.
Taking products of these quotients for successive word balls gives a
family whose kernels avoid every fixed nonidentity word eventually.  The
normalized character of each left-regular representation is the indicator
of its kernel, and hence converges pointwise to the regular character of
`BS(1,9)`.

The substitution `t=a` satisfies `[t,a]=1` identically and changes no
Baumslag--Solitar relation.  Since

```text
[a,h]=a h a^(-1)h^(-1)
```

is a nontrivial reduced element of `BS(1,9)`, its image is nonidentity in
all sufficiently late separating quotients.  Its regular matrix trace is
therefore zero.  This proves the claim with zero relator defect in every
matrix size used.
