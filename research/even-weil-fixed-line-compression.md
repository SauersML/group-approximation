---
rg: 2
id: even-weil-fixed-line-compression
kind: claim
title: The even Weil fixed line compresses to an O(p^-1/2) Iwahori near-extension with exact BS14 core
distinct_from:
  prime-bs14-packet-extension-classification: that classifies exact scalar packets; this constructs a reducible exact BS core with no same-dimensional extension but vanishing presentation defect.
  bs14-relative-involution-extension-stability: that allows flexible padding; this proves such padding is essential and identifies the sharp one-dimensional boundary model.
  iwahori-cycle-packet-determinant-fence: determinant detects exact nonextension but cannot prevent this normalized-HS compression.
---

For every prime `p=1 mod 4`, the even Weil representation of
`PSL_2(F_p)` has dimension

```text
d=(p+1)/2
```

and, on the arithmetic BS(1,4) subgroup, splits as

```text
H = C delta_0 (+) H_0,       dim H_0=(p-1)/2.          (EWC1)
```

The line `C delta_0` is fixed by the parabolic `S` and preserved by the
diagonal implementer `R`; `H_0` is the sum of the nonzero fourth-power
spectral cycles.  Let `P` project onto `H_0`, let `Q=1-P`, and write the full
Weil involution as `X`.  Then

```text
A=PXP,
A^2-P=-P X Q X P,                                   (EWC2)
```

whose right side has rank at most one.  Functional calculus gives a
selfadjoint involution `X_0=sgn(A)` on `H_0` with

```text
||X_0-A||_(2,H_0) <= 1/sqrt(dim H_0).                 (EWC3)
```

Because `R,S` preserve `P`, compressing any one of the four fixed Iwahori
words loses only excursions through the one-dimensional `Q` corner.  Word
telescoping and `(EWC3)` therefore give a universal constant `C` such that

```text
max( ||X_0^2-I||_2,
     ||(X_0R)^2-I||_2,
     ||(X_0S^2)^3-I||_2,
     ||(X_0RS)^3-I||_2 )
  <= C/sqrt(p).                                       (EWC4)
```

The BS core `(R,S)|_(H_0)` is exact.  It has no exact same-dimensional
Iwahori extension: `S` has primitive `p`-spectrum, so any such extension
would factor through `PSL_2(F_p)`, whose smallest nontrivial complex degree
is `(p+1)/2>dim H_0`.  Adding back the single line `C delta_0`, however,
recovers the exact Weil representation.

## Meaning for the open repair problem

Strict same-dimensional relative repair is false.  The flexible formulation
in `bs14-relative-involution-extension-stability` survives, but the example
fixes its necessary scale: defect `Theta(d^(-1/2))` can encode exactly one
missing dimension, so the correct reconciliation estimate is quadratic,
`padding/d = O(defect^2)`.  Any proposed positive-density packet gap that
forbids `(EWC4)` is false.
