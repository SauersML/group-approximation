---
rg: 2
id: two-matchings-force-full-weyl-on-multiplicity-free-spectra
kind: claim
title: Two field matchings force the full Weyl dimension on multiplicity-free spectra
distinct_from:
  two-field-matchings-rigidify-linear-weyl-mislabels: that treats one global linear translation error; this allows arbitrary nonlinear changes of eigenbasis but assumes rank-one spectral atoms.
  bounded-degree-entangled-agreement-pauli-metapixel: that asks for robust finite-template game soundness; this is the exact mixed-sampler algebra after same-basis decoding.
---

Let `V=F_2^n` with a nondegenerate symmetric pairing `<.,.>`.  Let
`T_0=I` and let `T_1=A` be self-adjoint with irreducible characteristic
polynomial.  Write the two characteristic-two quadratic forms as linear
characters

```text
<T_i b,b> = <c_i,b>,                                           (TM1)
```

and put `d_i=T_i^(-*)c_i`.

Let `U,W:V->U(H)` be exact unitary representations.  Assume their spectral
PVMs are multiplicity-free: after identifying the character group with `V`,

```text
U(a)e_x=(-1)^<a,x> e_x       (x in X subset V),
W(b)f_y=(-1)^<b,y> f_y       (y in Y subset V),                (TM2)
```

where all spectral atoms are one-dimensional.  Suppose that for every
`b in V` and `i in {0,1}`,

```text
U(T_i b) W(b)
  = (-1)^<T_i b,b> W(b) U(T_i b).                              (TM3)
```

Then

```text
X=Y=V,                    dim(H)=2^n.                           (TM4)
```

Thus the union of the two perfect matchings

```text
a=b,                       a=A b                               (TM5)
```

already rules out every bounded-dimensional nonlinear permutation/change-of-
basis model with simple same-basis spectra.  The complete X/Z pair table is
not needed in this sector.

The statement is exact.  Extending it to arbitrary spectral multiplicities
and then robust normalized-HS relations is isolated in
`two-matching-matrix-block-propagation`.
