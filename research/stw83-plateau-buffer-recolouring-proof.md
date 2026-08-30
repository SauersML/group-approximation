---
rg: 2
id: stw83-plateau-buffer-recolouring-proof
kind: route
title: Merge compatible plateau colours and compress a block-diagonal scheme to the complementary circle corner
target: stw83-plateau-buffer-recolouring-hinge
requires:
  - stw83-canonical-circle-toeplitz-dimension-two-bound
---

## Why the plateau condition gives two global colours

Use the notation and the intermediate Brake--Winter approximation from
`stw83-coefficient-toeplitz-three-colour-proof`.  Before approximating the
inner corner, it has two cpc order-zero outgoing maps:

```text
Theta^(0):F^(0)->A_N,
Theta^(1):F^(1)->C,
C=closure((1-tilde(h))A_N(1-tilde(h))).                 (2)
```

The first map merges the scalar transition band with the first quotient
colour; the second is the tail colour.  Since `p` is contained in the common
one-plateau of `h` and `tilde(h)`, both the transition band and the tail are
orthogonal to `p`.  The order-zero lift defining `Theta^(0)` may be taken in
the hereditary complement of `p`: the map before lifting already lands in
the product of those complements, and the standard finite-dimensional
order-zero lifting theorem applies to that quotient.  Hence

```text
Theta^(0)(F^(0)) eta^(0)(G^(0))=0.                      (3)
```

The relation `tilde(h)h=h` says that `tilde(h)` is one on `supp(h)`.
Therefore the whole inner corner `D` is orthogonal to the tail corner `C`, so

```text
Theta^(1)(F^(1)) eta^(1)(G^(1))=0.                      (4)
```

Sums of cpc order-zero maps with orthogonal ranges are cpc order zero.  Thus

```text
Theta^(0) direct-sum eta^(0),
Theta^(1) direct-sum eta^(1)                            (5)
```

are two outgoing colours.  Taking the direct sum of the corresponding cpc
incoming maps and first making the intermediate Toeplitz error and then the
inner-corner error small proves `dim_nuc(A_N)<=1`.  The quotient onto `C(T)`
gives the reverse inequality, proving (1).

This argument permits the coefficient-varying compact parts of a prescribed
finite set to be moved into a deep plateau before the scalar transition.  It
does not assume that `(PL)` holds for every element of the growing matrix
corner.

## The block-diagonal whole-corner no-go

Let `D=M_r(C(T))`, let `0<p<1` be constant, and put `q=1-p`.  Assume that a
net as in `(BD)` approximates `id_D`.  Restrict its incoming maps to
`qDq`.  The first outgoing colour disappears after compression because
`q(pDp)q=0`.  Since `q` commutes with the range of `eta^(1)`,

```text
x |-> q eta^(1)(x) q
```

is again cpc order zero.  Consequently the restricted and compressed maps
give one-colour finite-dimensional approximations of `id_(qDq)`.  Hence

```text
dim_nuc(qDq)=0.                                          (6)
```

But `q` has positive constant rank, so

```text
qDq = M_s(C(T))
```

for some `s>=1`.  Matrix stability and the commutative computation of nuclear
dimension give `dim_nuc(qDq)=dim(T)=1`, contradicting (6).  This proves the
no-go assertion.

The contradiction is specifically to a whole-corner, block-diagonal scheme.
It does not dispose of `(PL)`: a finite-set adaptive second colour may carry
off-diagonal scalar matrix terms across the plateau boundary, and constructing
such maps is the remaining analytic problem.
