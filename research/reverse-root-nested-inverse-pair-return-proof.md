---
rg: 2
id: reverse-root-nested-inverse-pair-return-proof
kind: route
title: Expand the nested reverse-root and inverse-pair commutators and audit their chart gauge
target: nested-inverse-pair-returns-signed-source-with-free-sign
requires:
  - actual-mixed-complement-returns-reverse-root
  - signed-hecke-normalizer-has-eight-external-root-returns
---

Write all commutators as `xyx^{-1}y^{-1}`.  In characteristic two every
root element displayed below is an involution.  The only nonzero ordered
coefficient product in the inner commutator is

```text
t_0s_0=1,
```

so the ordinary non-opposite Steinberg relation gives

```text
[x_75(t_0),x_56(s_0)]=x_76(1).
```

For the outer commutator the only ordered matrix-unit product is
`E_97E_76=E_96`, while the reverse product is zero.  Therefore

```text
[x_97(1),x_76(1)]=x_96(1).
```

The full ten-generator signed test in the MSI artifact confirms that
`x_97(1)`, `x_75(t_0)`, and `x_56(s_0)` do not normalize the signed pair,
whereas both `x_76(1)` and `x_96(1)` do.  Membership of the first as a
positive generator and of the second in the external list identifies the
characters, not merely the subgroup supports.

For the scoped gauge model, in two-by-two block notation put

```text
A=[[0,I],[I,0]],
U=diag(I,X),       V=diag(I,Z),       Q=diag(I,0).
```

Here `X,Z` are the two Pauli involutions.  Direct multiplication gives

```text
[U,V]=diag(I,-I),
[A,[U,V]]=diag(-I,-I).
```

The first commutator is the identity on `QH`; the second preserves `QH`
but restricts there as `-I`.  All five displayed operators are exact
finite-dimensional involutions.  This proves that the local nested-return
table leaves a free nontrivial external-return sign, so `(ESB2)` cannot be
read off from the exact source return alone.

The artifact checks both prefix-matrix identities and the integer
four-by-four chart model exactly.
