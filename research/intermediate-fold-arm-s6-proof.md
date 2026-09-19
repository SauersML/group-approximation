---
rg: 2
id: intermediate-fold-arm-s6-proof
kind: route
title: Verify the transported intermediate arm in six permutations
target: intermediate-fold-arm-has-finite-s6-model
requires: []
---

Use commutator convention `[x,y]=xyx^(-1)y^(-1)`.  All eight displayed
permutations in `(IFA4)` are involutions.  The factors in `C_0` and `C_1`
commute, and cancellation of their shared transposition gives

```text
C_0C_1=(1 2)(4 5)(3 6)(4 5)=(1 2)(3 6)=J.            (1)
```

Conjugating the two transpositions of `S` by `C_0` gives

```text
C_0 S C_0=(3 5)(4 6).
```

Multiplication by `S` then yields

```text
[C_0,S]=(3 5)(4 6)(3 4)(5 6)=(3 6)(4 5)=E.           (2)
```

The elements `C_1=E` and `S` are the two nonidentity generators of the
Klein four group on `{3,4,5,6}`, so `[C_1,S]=1`.  Since `J=C_0C_1`, while
`C_1` commutes with both `C_0` and `S`, equation `(2)` also gives
`[J,S]=E`.

The transposition `T=(5 6)` commutes with `S=(3 4)(5 6)`.  Conjugating `E`
by `T` changes it to `(3 5)(4 6)`, and hence

```text
[T,E]=(3 5)(4 6)(3 6)(4 5)=(3 4)(5 6)=M.             (3)
```

Finally, `W=(4 6)` is an involution and sends the two unordered pairs
`{3,4},{5,6}` to `{3,6},{5,4}`.  Therefore

```text
WSW^(-1)=(3 6)(4 5)=E.                               (4)
```

This verifies every shared occurrence in `(IFA1)--(IFA3)`.  The generated
subgroup of `S_6` is finite and `M` is nonidentity.  Its left regular
representation satisfies the entire table with zero defect and has
`||lambda(M)-1||_op=2` because `M` is a nonidentity involution.

