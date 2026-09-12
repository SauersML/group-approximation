---
rg: 2
id: steinberg-schur-four-transform-reduction-fails-p-seven-check
kind: claim
title: The proposed Steinberg four-transform reduction fails its p=7 consistency check
artifacts:
  - research/steinberg-schur-four-transform-p-seven-check.md
invalidates:
  - steinberg-schur-four-transform-resonance-attack
distinct_from:
  steinberg-rank-one-schur-pivot-is-invertible: this refutes the proposed SRP4 reduction, not the original determinant claim SRP1, whose p=7 matrix is nonsingular.
---

**ESTABLISHED FIREWALL.**  Direct evaluation of the original matrix formula
`(SRP2)` at `p=7` gives

```text
M_7 = [[0,0,0,1],
       [3,2,3,4],
       [5,3,1,5],
       [2,5,1,5]],

det(M_7)=4 != 0.                                      (S47F1)
```

But literal evaluation of the proposed correction formula `(SRP4)` gives

```text
H = [[3,6,1],
     [4,5,1],
     [5,3,0]],

I+H = [[4,6,1],
       [4,6,1],
       [5,3,1]],                                      (S47F2)
```

which is singular.  Therefore the assertion `det(M_p)=det(I+H)` with
`H` as in `(SRP4)` is false.  Every binary-form, parity, or resonance
reduction derived from that assertion is blocked until its indexing or
binomial-inversion error is found and corrected.  In fact the exact cofactor
calculation identifies the error.  After deleting row `r=2` and column
`i=p-2`, and reversing the remaining rows via `j=p-r`, the matrix is

```text
N'=W'+K',

W'_(j,v)=(-1)^j 2^(1-j-v)
 [binom(j+v-1,j)-1_(v>=j)binom(v,j)],

K'_(j,v)=1_(j+v=p)(2^(1-2v)-1).                      (S47F3)
```

Thus the dense part is not the asserted separable anti-Pascal matrix, and
the diagonal correction becomes anti-diagonal after row reversal.  This
check does **not** refute invertibility of the original Schur pivot.

DERIVATION
steinberg-schur-four-transform-p-seven-check
