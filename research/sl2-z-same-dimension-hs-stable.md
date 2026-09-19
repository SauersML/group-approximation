---
rg: 2
id: sl2-z-same-dimension-hs-stable
kind: claim
title: SL2(Z) is same-dimension Hilbert--Schmidt stable by cyclic spectral rounding
distinct_from:
  iwahori-local-global-defect-question: that asks to glue two exact SL2(Z) representations across an almost-matched Iwahori edge; this rounds each vertex representation separately and makes no assertion about their edge compatibility.
  finite-schur-clifford-packet-flexible-hs-exactification: that exactifies one fixed finite packet after a complete approximate multiplication table; this uses the cyclic-amalgam presentation of the infinite virtually free group SL2(Z).
---

Use the presentation

```text
SL_2(Z)=<s,r | s^4=1, s^2=r^3>,                    (SZS1)
```

where the common element is `-I`.  There is a universal modulus
`omega(epsilon)->0` such that, whenever unitaries `S,R in U(d)` satisfy

```text
||S^4-I||_2<=epsilon,
||S^2-R^3||_2<=epsilon,                              (SZS2)
```

there are unitaries `S_0,R_0 in U(d)` with

```text
S_0^4=I,                 S_0^2=R_0^3,
||S-S_0||_2+||R-R_0||_2<=omega(epsilon).             (SZS3)
```

Thus `SL_2(Z)` is Hilbert--Schmidt stable without changing dimension.

The construction is explicit.  Spectrally round `S` to the nearest fourth
root of unity, obtaining `S_0`, and put `Z=S_0^2`.  Then `Z` is an
involution and `R^3` is close to `Z`.  Since `R` commutes with `R^3`, it
almost commutes with `Z`.  Delete the two off-diagonal blocks of `R` relative
to the spectral projections of `Z`, polar-round the diagonal compression to
a unitary `Q` commuting with `Z`, and finally round the spectrum of `Q` on
the `Z=+1` block to the cube roots of `+1` and on the `Z=-1` block to the
cube roots of `-1`.  The resulting `R_0` satisfies `R_0^3=Z`.

The modulus can be taken linear.  Let `c_k` bound, on the unit circle,
distance to the nearest root of `z^k=lambda` by
`c_k|z^k-lambda|`.  Then `||S-S_0||_2<=c_4 epsilon`.  If
`alpha=||R^3-Z||_2`, then `alpha<=(1+2c_4)epsilon` and

```text
||[R,Z]||_2<=2alpha.                                  (SZS4)
```

For `E_+-E_-=Z`, put `D=E_+RE_++E_-RE_-`.  Orthogonality of the two
off-diagonal blocks gives

```text
||R-D||_2=(1/2)||[R,Z]||_2<=alpha.                    (SZS5)
```

The block polar unitary `Q` may be chosen with
`||D-Q||_2<=||I-D^*D||_2<=2alpha`; hence
`||Q-R||_2<=3alpha` and `||Q^3-Z||_2<=10alpha`.  Spectral rounding on the
two `Z` blocks gives `||Q-R_0||_2<=10c_3 alpha`.  Thus one may take

```text
omega(epsilon)
 <=c_4 epsilon+(3+10c_3)(1+2c_4)epsilon.             (SZS6)
```

All constants are independent of dimension.
