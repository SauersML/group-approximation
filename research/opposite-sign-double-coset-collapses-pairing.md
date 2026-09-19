---
rg: 2
id: opposite-sign-double-coset-collapses-pairing
kind: claim
title: An opposite-sign stabilizer double coset collapses the coinvariant pairing certificate
distinct_from:
  cayley-module-bilinear-certificate-protects-pauli-mark: that gives the complete positive coinvariant criterion; this identifies its first unavoidable two-prototype obstruction as a stabilizer double-coset collision.
  sign-double-cosets-separate-pauli-clouds: that uses separated cosets to prove cloud injectivity; this works directly in quotient Cayley modules and does not assume a coset permutation model.
  oligomorphic-gl-has-unbounded-stabilizer-fillings: that is a quantitative word-area obstruction for global sections; this is an exact algebraic obstruction even before any Hilbert--Schmidt estimate.
---

Let `A` act on binary modules `M_X,M_Z`, fix `x in M_X` and `z in M_Z`,
and put

```text
H_X={a in A:a x=x},             H_Z={a in A:a z=z}.       (OSD1)
```

For two mixed offsets `p_0,p_1 in A`, set

```text
c_b=[x tensor p_b z] in (M_X tensor_F2 M_Z)_A.            (OSD2)
```

If

```text
p_0 in H_X p_1 H_Z,                                      (OSD3)
```

then `c_0=c_1`.  Consequently no `A`-invariant bilinear form can satisfy

```text
beta(x,p_0 z)=0,             beta(x,p_1 z)=1.             (OSD4)
```

Equivalently, the two prescribed signs already violate `(CBP4)` of
`cayley-module-bilinear-certificate-protects-pauli-mark`: the dependence
`c_0+c_1=0` has prescribed value `0+1=1`.

The criterion also has a path form.  If some `a in A` fixes `x` in the
X quotient and transports the sign-one Z endpoint to the sign-zero endpoint,

```text
a x=x,                    a p_1 z=p_0 z,                  (OSD5)
```

then the two prototype tensors coincide.  Thus an equality-cloud path whose
closed address holonomy has `(OSD5)` is fatal regardless of its length,
girth, or local congestion.  In particular, avoiding every bounded contour
does not imply sign safety: the required statement is the global double-
coset separation

```text
H_X p_0 H_Z  intersect  H_X p_1 H_Z = empty.              (OSD6)
```

for the stabilizers induced by the **quotient modules**, not merely for the
free address group before the same-basis relations are imposed.

This is an obstruction, not a construction.  Natural vector/covector
modules for a finitary linear actor avoid it algebraically because evaluation
is invariant and the two pairing values are different.  They do not thereby
solve finite-orbit placement: turning contextual transporters into fixed
occurrence words still introduces stabilizer word equalities of unbounded
area, as recorded by `oligomorphic-gl-has-unbounded-stabilizer-fillings`.
