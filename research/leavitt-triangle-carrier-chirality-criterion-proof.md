---
rg: 2
id: leavitt-triangle-carrier-chirality-criterion-proof
kind: route
title: Compare the two signs on each edge of the oriented triangle
target: leavitt-triangle-carrier-chirality-criterion
requires: []
---

Use canonical faces

```text
P A Q,       Q^-1 B R,       R^-1 C P^-1.
```

Let `ci` be the normal/inverse chirality of face `i`; inversion reverses all
carrier exponents on that face.  The two occurrences of `P` have opposite
signs exactly when `c0=c2`.  Similarly `Q` closes exactly when `c0=c1`, and
`R` closes exactly when `c1=c2`.  All three close if and only if

```text
c0=c1=c2.
```

If this fails, eliminating the matched carrier variables leaves a word
containing a carrier.  For example the chirality `(N,N,I)` gives faces

```text
P A Q,       Q^-1 B R,       P C^-1 R^-1,
```

and elimination yields `P C^-1 P A B`, not `ABC`.  Vanishing of its abelian
carrier projection cannot justify replacing this nonabelian holonomy by a
coefficient-only word.

