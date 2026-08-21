---
rg: 2
id: nonhyperlinear-via-affine-leavitt-coefficient-decoder
kind: route
title: Collapse the affine active root through one decoded relative Leavitt cell
target: non-hyperlinear-group
requires:
  - affine-active-corner-has-faithful-binary-leavitt-envelope
  - affine-leavitt-steinberg-mark-is-fd-invisible
  - approximate-relative-leavitt-cell-kills-active-trace
  - affine-leavitt-steinberg-hs-coefficient-decoder
---

Let

```text
Gamma_A=St_5(L_A(k[C_aff])),       w_A=x_12(A).
```

The first two claims give a finitely presented property-`(T)` group and a
nontrivial word `w_A`. Apply the coefficient decoder to any normalized-HS
microstate of `Gamma_A`. The decoded relative Leavitt relations and the
dimension-free trace inequality give

```text
tr(P)<=3omega(delta).
```

The mark-comparison inequality then gives

```text
||w_A(U)-I||_2 -> 0.                                      (NAC1)
```

If `Gamma_A` were hyperlinear, microstates for its canonical delta trace
would instead satisfy

```text
||w_A(U)-I||_2^2 -> 2
```

because `w_A!=1`. This contradicts `(NAC1)`. Thus the decoder would make the
already explicit finitely presented group `Gamma_A` nonhyperlinear; no
Higman embedding, recursive tape, or dimension-reporting layer would remain.
