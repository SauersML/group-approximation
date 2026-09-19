---
rg: 2
id: center-chain-scalar-gram-polar-cut-proof
kind: route
title: Compute the two arm overlaps with the chained character atom
target: center-chain-scalar-gram-polar-cut-returns-moving-atom
requires:
  - center-chain-character-atom-gives-scalar-gram
  - finite-character-hecke-intersection-formula
  - two-transport-cross-gram-has-a-fixed-mass-reducing-corner
---

Use the six independent positive-root coordinates for `H` on the ordered
indices `(6,5,4,2)`:

```text
65, 54, 42, 64, 52, 62.                                (MPP1)
```

Every coordinate has coefficient `0` or `q`, so these coordinates give the
sixty-four elements of `H`.  Conjugation by `A_1=x_47(a_1)` changes precisely
the coordinates whose terminal index is `4`.  Since `qa_1=a_1`, it adds the
outside coordinates

```text
54 -> 57,                         64 -> 67.             (MPP2)
```

The two new root positions are distinct and neither belongs to `(MPP1)`.
Elementary-matrix normal form therefore gives

```text
H cap A_1 H A_1^(-1)={h in H:h_54=h_64=0},
|H cap A_1 H A_1^(-1)|=2^4=16.                         (MPP3)
```

On this intersection `A_1` actually centralizes `h`; hence `chi` and its
transport agree.  The finite-character Hecke formula yields

```text
||e A_1 e||_2^2=16/64^2=1/256.                         (MPP4)
```

Similarly, conjugation by `A_2=x_58(a_2)` changes only the `65` coordinate,
adding the outside root `68`, because `qa_2=a_2`.  Thus

```text
H cap A_2 H A_2^(-1)={h in H:h_65=0},
|H cap A_2 H A_2^(-1)|=2^5=32,                         (MPP5)
```

and `A_2` centralizes this intersection.  Character compatibility and the
same formula give

```text
||e A_2 e||_2^2=32/64^2=1/128.                         (MPP6)
```

For a projection `e` and a unitary `A`, traciality gives

```text
||[e,A]||_2^2=2 tau(e)-2 Re tau(e A e A^*).            (MPP7)
```

Substituting `tau(e)=1/64` and `(MPP4)`--`(MPP6)` proves the two constants in
`(MPC3)`.

Finally the selector roots `g_1,g_2` centralize `e`, so

```text
(S_1^*S_2)^*(S_1^*S_2)
=e g_2^* g_1 e g_1^* g_2 e=e.                         (MPP8)
```

The spectral projection `1_[t,1](e)` equals `e` for every `0<t<=1`.  Hence
the cross-Gram polar cut has no freedom to discard the fixed arm-moving
part measured in `(MPP7)`.  This proves the claim.

