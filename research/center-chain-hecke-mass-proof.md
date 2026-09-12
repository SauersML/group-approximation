---
rg: 2
id: center-chain-hecke-mass-proof
kind: route
title: Count fixed unitriangular coordinates under the two external arms
target: center-chain-hecke-arms-have-native-masses
requires:
  - center-chain-character-atom-gives-scalar-gram
  - finite-character-hecke-intersection-formula
---

Write an element of `H` by its six upper-unitriangular matrix coordinates on
the ordered vertices `(6,5,4,2)`.  Conjugating by
`A_1=I+a_1E_47` adds the external coordinates

```text
(6,7)=h_(6,4)a_1,             (5,7)=h_(5,4)a_1.       (CHP1)
```

The two coefficients vanish exactly when `h_(6,4)=h_(5,4)=0`: elementary
matrix positions prevent cancellation with an element of `H`, and `a_1` is
nonzero.  Hence

```text
|H intersect A_1HA_1^(-1)|=2^(6-2)=16.                (CHP2)
```

On this intersection conjugation by `A_1` is the identity, so the two
character restrictions agree.

The roots `A_1=x_47(a_1)` and `A_2=x_58(a_2)` commute.  Conjugation by
`A_2=I+a_2E_58` adds the further external coordinate

```text
(6,8)=h_(6,5)a_2.                                     (CHP3)
```

Thus conjugation by `A_2A_1` lands back in `H` exactly when the three
independent coordinates `(6,4),(5,4),(6,5)` vanish.  It fixes every element
of that intersection, and therefore

```text
|H intersect (A_2A_1)H(A_2A_1)^(-1)|=2^(6-3)=8.       (CHP4)
```

Apply `(FCH3)` with `K=H`, the same character at both ends, and respectively
`g=A_1,A_2A_1`.  Since `|H|=64`,

```text
||e g e||_2^2=|H intersect gHg^(-1)|/|H|^2,
```

which is `16/64^2=1/256` and `8/64^2=1/512`.  Dividing by
`tau(e)=1/64` proves `(CHA2)`.

