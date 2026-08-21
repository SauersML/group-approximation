---
rg: 2
id: one-coarse-to-fine-prefix-isometry-closes-the-reservoir
kind: claim
title: One coarse-to-fine prefix isometry is a complete same-reservoir certificate
distinct_from:
  rectangular-wedderburn-block-isometry-gap: that compares unequal irreducible Fourier corners in a regular finite-group chart; this compares the actual coarse and fine Leavitt matrix-unit systems with one common active identity and constructs the bridge exactly in the properly infinite completeness model.
  diagonal-leavitt-prefix-transport-cannot-carry-cross-corners: that rules out using an off-diagonal prefix coefficient as a rootwise ring endomorphism; this uses one such coefficient as a rectangular Morita arrow, for which multiplicativity is neither asserted nor needed.
  whitehead-swap-copy-completion-retains-rectangular-escape: that shows diagonal amplification still changes the reservoir; this gives the first explicit off-diagonal cell which detects that change.
  four-pauli-standard-polynomial-gives-a-fixed-rectangular-gap: that needs all four returned target words confined to one source factor; this needs only one coarse-to-fine Gram relation between two already exactified matrix-unit packets.
---

**ESTABLISHED.**  Let `M=M_d(C)`, let `P in M` be a projection, and let

```text
(e_ij)_(1<=i,j<=r),       (f_ab)_(1<=a,b<=s)           (CFI1)
```

be two exact systems of matrix units with the same identity `P`.  Assume
`r<s`, put `e=e_11`, `f=f_11`, and let `X=fXe` be any rectangular operator.
Then

```text
||e-X^*X||_2^2 >= tr(P)(1/r-1/s),                     (CFI2)

tr(P) <= rs/(s-r) ||e-X^*X||_2^2.                     (CFI3)
```

Indeed `rank(e)=rank(P)/r`, `rank(f)=rank(P)/s`, and
`rank(X^*X)<=rank(f)`.  On a subspace of `eH` of dimension at least
`rank(e)-rank(f)`, the operator `X^*X` vanishes and `e-X^*X` is the
identity.  This proves `(CFI2)` without an operator-norm hypothesis on `X`.

For the first binary Leavitt return, `r=2` and `s=4`, so

```text
||e-X^*X||_2^2 >= tr(P)/4,
tr(P) <= 4 ||e-X^*X||_2^2.                             (CFI4)
```

Thus one approximate isometry from a coarse minimal corner to a fine minimal
corner is already a dimension-free same-reservoir certificate.  It is
strictly smaller than recovering a mutual bicommutant, transporting the
whole commutant averaging projection, or placing the full two-qubit tuple
inside the source `M_2` factor.

## The bridge exists exactly in the Leavitt completeness model

In a relative binary Leavitt corner, use the depth-one and depth-two matrix
units

```text
e_ij=s_i t_j,                    f_(u,v)=s_u t_v.       (CFI5)
```

They both sum to the active identity `A`.  For the coarse leaf `0` and its
fine descendant `00`, put

```text
x=s_(00)t_0,                     y=s_0t_(00).           (CFI6)
```

Prefix cancellation gives

```text
yx=e_(0,0),                      xy=f_(00,00).           (CFI7)
```

Hence `x` is precisely the coarse-to-fine rectangular Morita isometry which
finite matrices cannot support at positive active trace.  There is no
completeness obstruction: in the properly infinite Leavitt module the two
corners are equivalent even though one belongs to a two-piece decomposition
and the other to a four-piece decomposition.

The bridge also has a fixed ordinary elementary word.  Over characteristic
two define

```text
J_x=[[1-f, x],
     [y, 1-e]].                                         (CFI8)
```

Then `J_x^2=1`, and exactly

```text
J_x = [[1,x],[0,1]] [[1,0],[y,1]] [[1,x],[0,1]].        (CFI9)
```

Thus the required stabilized cell is not an unspecified large Morita table:
it is one depth-two prefix coefficient and a three-root partial-swap word.
The crossed prefix map is not being applied rootwise, so the
nonmultiplicativity obstruction for `a |-> s_u a t_v` does not apply.

## Remaining authentication interface

In a finite normalized-HS microstate, exactify the fixed source `M_2` and
target `M_4` Pauli packets on one selected projection `P`.  It is sufficient
to decode the off-diagonal block of the one word `(CFI9)` as an operator
`X=fXe` satisfying

```text
||e-X^*X||_2=o(1).                                     (CFI10)
```

Then `(CFI4)` forces `tr(P)=o(1)`.  Consequently the former
same-reservoir problem has a minimal finite target: authenticate one
coarse-to-fine Gram row on the common marked carrier.  Diagonal Whitehead
transport does not provide `(CFI10)`, but no simultaneous family of all
off-diagonal bimodules is necessary either.

