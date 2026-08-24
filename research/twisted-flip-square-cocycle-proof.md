---
rg: 2
id: twisted-flip-square-cocycle-proof
kind: route
title: Compute the quotient cocycle and its sharp Hilbert--Schmidt dilution
target: twisted-flip-square-shifts-multiplicity-cocycle
requires: []
---

Schur's lemma gives

```text
u=A tensor R,                 v=D tensor S              (TFP1)
```

on the invariant `T`-isotypic carrier. Using the group-commutator
convention `[x,y]=xyx^(-1)y^(-1)` and `(TFS1)`,

```text
[u,v]=[A,D] tensor [R,S]
     =zeta I_T tensor [R,S].                            (TFP2)
```

The right side of the relator in `(TFS2)` is
`omega I_T tensor I_m`, so `(TFP2)` is equivalent to `(TFS3)`.
Taking determinants and using `det([R,S])=1` gives

```text
1=(omega zeta^(-1))^m.                                  (TFP3)
```

If the quotient scalar has order `r`, equation `(TFP3)` says `r|m`.

For sharpness, write `m=qr+s` with `0<=s<r`. On `C^(qr)`, take `q`
copies of the standard `r`-dimensional clock-and-shift pair having scalar
commutator `lambda=omega zeta^(-1)`. Extend both unitaries by the identity
on `C^s`. The commutator is `lambda I` on `C^(qr)` and `I` on `C^s`.
Therefore

```text
||[R,S]-lambda I||_(2,m)^2
 =s |1-lambda|^2/m
 <=4(r-1)/m,                                             (TFP4)
```

which tends to zero for fixed `r`. Finally substitute the Schur flip-square
cocycles: `zeta=-1` on a forbidden simple and `zeta=1` on the allowed orbit
sum. With `c=J` and `J=-1`, the quotient phases are respectively `1` and
`-1`, proving `(TFS5)` and the stated transfer of the parity burden.

