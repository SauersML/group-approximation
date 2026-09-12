---
rg: 2
id: exact-fd-invisibility-has-no-general-hs-robustification
kind: claim
title: Exact finite-dimensional invisibility has no general normalized-HS robustification
distinct_from:
  hs-stability-plus-fd-residual-forces-nonhyperlinearity: that adds uniform flexible normalized-HS stability and thereby obtains robust collapse; this proves that the stability hypothesis cannot be inferred from exact invisibility, finite presentation, or even soficity.
  slofstra-involution-not-sofic-radical: that constructs a sofic image detecting a mark in Slofstra's later solution group; this uses the explicitly finitely presented sofic group of Slofstra--Vidick Proposition 3.2 and records the direct obstruction to a universal robustification theorem.
  cyclic-base-sharpness: that uses an amenable Clifford quotient for a different compression mark; this imports a published finitely presented sofic example with a central involution killed in every exact finite-dimensional representation.
---

There is a finitely presented sofic group `K` and a nontrivial central
involution `c in K` such that

```text
pi(c)=I
```

for every finite-dimensional unitary representation `pi` of `K`, while
canonical sofic, hence normalized-HS, microstates keep `c` separated from the
identity.

One may take the group in Slofstra--Vidick, arXiv:1711.10676, Proposition 3.2:

```text
K=<a,b,c,x,y |
   xyx^(-1)=y^2, xcx^(-1)=c,
   yay^(-1)=b, yby^(-1)=a,
   c=ab, a^2=b^2=c^2=1>.
```

The paper states immediately after Proposition 3.2 that `K` is sofic, `c` is
a central involution trivial in every finite-dimensional representation, and
then proves finite upper and lower bounds for the hyperlinear profile of `c`.

Consequently there is no theorem of the form

```text
finite presentation + exact finite-dimensional invisibility of w
  => ||w(U)-I||_2 <= omega(def(U)),  omega(t)->0,       (EFI1)
```

valid for arbitrary groups.  Applying `(EFI1)` to `K,c` would collapse the
same word in its sofic microstates, contradicting their canonical trace
separation.  Any successful upgrade for a Leavitt, Schur--Toeplitz, or
self-referential invisible mark must use extra structure that fails for this
example: uniform HS stability, a positive trace checksum, a common-carrier
inequality, or an equivalent matrix-coordinate hypothesis.

