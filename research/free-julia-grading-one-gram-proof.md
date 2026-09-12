---
rg: 2
id: free-julia-grading-one-gram-proof
kind: route
title: Read a Gram contraction and its mass from two involution commutators
target: free-julia-grading-carries-one-gram-at-canonical-quarter-mass
requires:
  - one-gram-vector-decodes-a-finite-bcs-strategy
---

Relative to `P_+H direct_sum P_-H`, write

```text
j=[[a,G],[G^*,b]],              d=diag(A,B).            (FJGP1)
```

Since `z=diag(1,-1)`,

```text
zj-jz=[[0,2G],[-2G^*,0]].                              (FJGP2)
```

Right multiplication by `zj` gives

```text
(zj-jz)zj=zjzj-1,
```

and normalized `L2` norm is invariant under multiplication by a unitary.
The two off-diagonal corners in `(FJGP2)` are orthogonal and have the same
trace, so

```text
||zjzj-1||_2^2
 =4||G||_2^2+4||G^*||_2^2
 =8||G||_2^2.                                          (FJGP3)
```

Similarly,

```text
d j-j d
 =[[[A,a],       AG-GB],
   [BG^*-G^*A,   [B,b]]].                              (FJGP4)
```

The four matrix corners are `L2`-orthogonal.  The two off-diagonal terms are
adjoints, whence

```text
||dj-jd||_2^2 >= 2||AG-GB||_2^2.                       (FJGP5)
```

Again `(dj-jd)dj=djdj-1`, proving the row estimate.

For a canonical microstate of a nontrivial `w_0`, canonical trace convergence
gives

```text
||w_0-1||_2^2=2-2 Re tau(w_0)=2+o(1).
```

Spectral rounding of the finitely many approximate involutions changes every
fixed word and every corner by `o(1)`.  Combining this with `(FJGP3)` yields
`||G||_2^2=1/4+o(1)`.

Finally, the defect-operator identity

```text
(1-GG^*)^(1/2)G=G(1-G^*G)^(1/2)                       (FJGP6)
```

proves directly that the matrix in `(FJG6)` squares to one.  If `AG=GB`,
then its adjoint gives `G^*A=BG^*`; multiplication yields commutation of `A`
with `GG^*` and of `B` with `G^*G`.  Functional calculus and `(FJGP6)` then
show `diag(A,B)j_G=j_Gdiag(A,B)`, completing the exact realization.

