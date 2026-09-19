---
rg: 2
id: rank-deficient-return-row-opnorm-proof
kind: route
title: Take a kernel vector of the compressed return and evaluate the complementary row on it
target: rank-deficient-return-row-has-operator-norm-one
requires: []
---

For `(ROW2)`, expand with `f+(1-f)=1` and use `J^*J=1`:

```text
X^*X+L^*L
 =eJ^*fJe+eJ^*(1-f)Je
 =eJ^*Je
 =e.
```

Both summands are positive, so `0<=e-X^*X=L^*L<=e<=1` and therefore
`||e-X^*X||_op<=1`.  Likewise `||L||_op<=1`, because `1-f`, `J` and `e` are
all contractions.

For the lower halves of `(ROW4)`, consider the linear map

```text
fJ|_(eH):eH->fH.
```

Its domain has dimension `rank(e)`, its codomain dimension `rank(f)`, and
`(ROW3)` says the first is strictly larger.  So the map is not injective:
choose a unit vector `xi in eH` with `fJxi=0`.  Then

```text
L xi=(1-f)Je xi=(1-f)J xi=J xi,
||L xi||=||J xi||=1,
```

since `J` is unitary.  Hence `||L||_op>=1`, and with the contraction bound
`||L||_op=1`.  Applying `(ROW2)` to the same vector,

```text
(e-X^*X)xi=L^*L xi,
<(e-X^*X)xi,xi>=||L xi||^2=1,
```

so `||e-X^*X||_op>=1` and hence `=1`.  Equivalently `X xi=fJxi=0`, so `X`
fails to be injective on `eH` and `e-X^*X` acts as the identity on
`ker(X) cap eH`, a subspace of dimension at least `rank(e)-rank(f)>=1`.

For `(ROW6)`: in an exact `r by r` system of matrix units with identity `P`,
the diagonal projections `e_ii` are Murray--von Neumann equivalent and sum to
`P`, so each has rank `rank(P)/r`; the same for `f_aa` with `s`.  In
particular `s` divides `rank(P)`, so `rank(P)>=s` whenever `P!=0`, and

```text
rank(e_11)-rank(f_11)=rank(P)(s-r)/(rs)>=(s-r)/r>=1/r.
```

The left side is an integer and is positive, hence at least `1`.  Now
`(ROW3)` holds and `(ROW7)` is `(ROW4)`.

Amplification-blindness is immediate from the same computation: on
`H tensor K` the kernel vector may be taken of the form `xi tensor eta`, and
`(J tensor 1)(xi tensor eta)` is again a unit vector orthogonal to the range
of `f tensor 1`.
