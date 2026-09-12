---
rg: 2
id: two-torus-denominator-multiplicity-proof
kind: route
title: Multiply two Steinberg rank-one torus words and retain the unbalanced denominator exponent
target: two-torus-closures-detect-denominator-multiplicity
requires: []
---

On the `(i,j)` coordinate plane, direct multiplication gives

```text
w_ij(a)=[[0,a],[-a^(-1),0]],
w_ij(a)w_ij(1)^(-1)=diag(a,a^(-1)).                    (TTD1)
```

Conjugation by `h=diag(p,1,p^(-1))` scales both negative simple
roots by `p^(-1)`:

```text
h x_21(-1)h^(-1)=x_21(-p^(-1)),
h x_32(-1)h^(-1)=x_32(-p^(-1)).                        (TTD2)
```

Substituting `(TTD2)` into `(TTC2)` and applying `(TTD1)` yields the two
diagonal matrices in `(TTC3)`.  Their product is `h`, proving `(TTC4)`.

For `(TTC5)`, every lattice letter acts trivially on `M` and every occurrence
of `h^(plusOrMinus1)` contributes `V^(plusOrMinus1)` there.  Each `D_ij`
has exponent zero, hence evaluates to `I_M tensor rho(D_ij)`.  The leading
`h^(-1)` in `R_tor` leaves exactly

```text
V^(-1) tensor rho(h)^(-1)rho(D_12D_23)
 =V^(-1) tensor I_K.                                   (TTD3)
```

Normalized Hilbert--Schmidt norm is unchanged by tensoring with an identity,
which proves `(TTC6)`.  For the two-dimensional rotation `H_0` in the
balanced counterpacket,

```text
||H_0-I||_2^2=2-2 Re tr_2(H_0)=2-sqrt(2),              (TTD4)
```

giving the displayed exact defect.
