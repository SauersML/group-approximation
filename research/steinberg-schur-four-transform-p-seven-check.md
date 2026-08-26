---
rg: 2
kind: route
id: steinberg-schur-four-transform-p-seven-check
title: Check the proposed Schur reduction directly at p=7 and correct its cofactor
target: steinberg-schur-four-transform-reduction-fails-p-seven-check
requires: []
---

# The p=7 consistency check for the proposed Schur reduction

All arithmetic is in `F_7`.  Substitution into the original entry formula
`(SRP2)`, with rows and columns indexed by `2,3,4,5`, gives

```text
M_7 = [[0,0,0,1],
       [3,2,3,4],
       [5,3,1,5],
       [2,5,1,5]].
```

Expanding along the first row leaves

```text
C = [[3,2,3],
     [5,3,1],
     [2,5,1]].
```

Its determinant is

```text
3(3-5)-2(5-2)+3(25-6)=45=3 mod 7.
```

The cofactor sign is `(-1)^(1+4)=-1`, so

```text
det(M_7)=-3=4 mod 7.
```

On the other hand, direct substitution of `u,v=2,3,4` into `(SRP4)` gives

```text
H = [[3,6,1],
     [4,5,1],
     [5,3,0]].
```

The first two rows of `I+H` are both `[4,6,1]`, hence
`det(I+H)=0`.  The two claimed determinants disagree.  The error is upstream
of every later four-transform identity, so those identities cannot serve as
a proof target without a corrected derivation from `(SRP2)`.

The exact source of the discrepancy is visible before inversion.  Delete
row `r=2` and column `i=p-2`, then reverse the remaining rows with `j=p-r`.
Writing `v=i`, direct substitution into `(SRP2)` gives

```text
W'_(j,v)=(-1)^j 2^(1-j-v)
 [binom(j+v-1,j)-1_(v>=j)binom(v,j)],

K'_(j,v)=1_(j+v=p)(2^(1-2v)-1).
```

For `p=7` these are

```text
W' = [[2,5,1],
      [5,3,5],
      [3,1,3]],

K' = [[0,0,0],
      [0,0,3],
      [0,1,0]].
```

In particular `det(W')=4`, not the claimed `-1/8=6`, and `K'` is
anti-diagonal rather than diagonal.  The old factorization
`W'_(j,v)=a_j binom(v,j)b_v` omitted the first binomial term and therefore
cannot be repaired downstream at the binary-form stage.
