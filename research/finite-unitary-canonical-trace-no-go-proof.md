---
rg: 2
id: finite-unitary-canonical-trace-no-go-proof
kind: route
title: Count the orthogonal group matrices and test the trivial-character multiplicity
target: finite-unitary-canonical-trace-span-no-go
requires: []
---

Condition `(FCT1)` first makes `rho` faithful.  For distinct `g,h`,

```text
<rho(g),rho(h)>_HS=tr_n(rho(g^(-1)h))=0.                (FCT2)
```

Thus `rho(K)` is an orthonormal set in the `n^2`-dimensional space `M_n`, so
`|K|<=n^2`.  Spanning requires at least `n^2` distinct matrices.  Therefore
`K` is finite, `|K|=n^2`, and `rho(K)` is an orthonormal basis.  Its span is
all of `M_n`, so the commutant is scalar and `rho` is irreducible.

For the ordinary character `chi=Tr rho`, condition `(FCT1)` gives
`chi(e)=n` and `chi(g)=0` off the identity.  The multiplicity of the trivial
representation is therefore

```text
<chi,1>=(1/|K|)sum_g chi(g)=n/n^2=1/n.                 (FCT3)
```

This must be a nonnegative integer, forcing `n=1`.  Faithfulness and
`(FCT1)` then make the represented group trivial.
