---
rg: 2
id: odd-leavitt-prefix-whitehead-transport
kind: claim
title: The native odd-characteristic prefix bridge is a signed Whitehead transport
distinct_from:
  one-coarse-to-fine-prefix-isometry-closes-the-reservoir: that proves the finite rank floor and writes an involutive three-elementary bridge in characteristic two; this supplies the exact signed bridge in the actual affine splitting characteristic p at least five.
  affine-active-doubling-is-elementary-matrix-conjugacy: that transports the whole active idempotent to two diagonal copies; this transports one coarse prefix atom to one fine descendant.
  literal-prefix-three-root-swap-retains-typed-carriers: that gives the typed-carrier countermodel for the unsigned characteristic-two swap; the same typed escape remains for this signed odd-characteristic word.
---

**ESTABLISHED.**  In the repository's relative binary Leavitt envelope over
the finite splitting field of characteristic `p>=5`, put

```text
e=s_0t_0,             f=s_(00)t_(00),
x=s_(00)t_0,          y=s_0t_(00).                     (OLW1)
```

Prefix cancellation gives

```text
yx=e,       xy=f,       xe=x=fx,       ey=y=yf.        (OLW2)
```

The signed three-elementary word

```text
W_x=E_12(x) E_21(-y) E_12(x)                           (OLW3)
```

is

```text
W_x=[[1-f, x],[-y,1-e]],
W_x^(-1)=[[1-f,-x],[y,1-e]],                           (OLW4)
```

and satisfies the exact same-object prefix transport

```text
W_x diag(0,e) W_x^(-1)=diag(f,0).                      (OLW5)
```

Thus the native odd-characteristic affine packet already contains a fixed
ordinary group word carrying a coarse minimal prefix corner to its fine
descendant.  Characteristic two was used only to make the unsigned word an
involution; neither invertibility nor the covariance `(OLW5)` requires it.

The verification is direct.  Multiplying `(OLW3)` and using `xy=f` and
`yx=e` gives `(OLW4)`.  Multiplying the two displayed matrices gives the
identity.  Finally

```text
W_x diag(0,e)=[[0,x],[0,0]],
```

and right multiplication by `W_x^(-1)` gives `diag(xy,0)=diag(f,0)`.

This closes a possible characteristic mismatch in the boundary program but
does not prove the decoder.  A finite matrix microstate assigns a unitary to
the elementary word `W_x`; it does not automatically decode `e` and `f` as
projections on one common packet carrier or turn `(OLW5)` into covariance of
their spectral selectors.  The typed rectangular model still evaluates the
word exactly with the two ambient packet identities kept distinct.  The
remaining native odd-characteristic lemma is therefore precisely selector
authentication (or a matrix-only payment for its failure), not discovery of
a return actuator.
