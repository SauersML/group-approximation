---
rg: 2
id: stw81-cross-orthogonal-near-partitions-force-projections
kind: route
title: Expand the complementary products and cut the resulting spectral gaps
target: stw81-projectionless-rotating-overlap-degeneracy
requires:
  - stw81-stationary-two-colour-interval-patching-forces-af
---

Set

```text
R=1-h_0-h_1,                    S=1-k_0-k_1.
```

These are positive contractions of norm at most `epsilon`.  From
`h_1k_1=0` and

```text
h_1=1-h_0-R,                    k_1=1-k_0-S
```

one obtains, without any commutativity assumption,

```text
(1-h_0)(1-k_0)=(1-h_0)S+R(1-k_0-S).                  (RTP1)
```

The final factor on the right is `k_1`, hence a contraction.  Since
`h_0k_0=0`, the left side is `1-h_0-k_0`.  Therefore

```text
norm(1-h_0-k_0)<=2epsilon.                            (RTP2)
```

Multiplication on the left by `h_0` gives

```text
norm(h_0-h_0^2)
 =norm(h_0(1-h_0-k_0))<=2epsilon.                     (RTP3)
```

Positive orthogonality is symmetric, so multiplication on the left by
`k_0` gives the same estimate for `k_0`.  Interchanging the labels zero and
one and starting from `h_0k_0=0` proves the estimates for `h_1` and `k_1`.
This proves (RTO2).

For a positive contraction `x` satisfying

```text
norm(x-x^2)<=2epsilon,              epsilon<1/8,
```

the scalar inequality `t(1-t)<=2epsilon` on `spectrum(x)` gives

```text
spectrum(x) subset [0,alpha] union [1-alpha,1],
alpha=(1-sqrt(1-8epsilon))/2.                         (RTP4)
```

Thus the spectral projection

```text
p=1_[1/2,1](x)
```

belongs to `C*(x,1) subset D`.  If `D` is projectionless, `p` is zero or
one.  Applied to `h_0`, the first case gives `norm(h_0)<=alpha`.  In the
second case `norm(1-h_0)<=alpha`, and

```text
0<=h_1<=1-h_0
```

gives `norm(h_1)<=alpha`.  In either case one support of the `h`-frame has
norm at most `alpha`; since its total is within `epsilon` of one, the other
is within `alpha+epsilon` of one.  The same argument applies to the
`k`-frame.

We finally verify the approximation consequence without assuming that the
total return is contractive.  Write one ordinary piecewise-c.p.c.
two-colour factorization as

```text
D --psi--> F_0 direct_sum F_1 --phi_0+phi_1--> D,
a_i=phi_i(psi_i(1_D)).                               (RTP5)
```

Each `a_i` is a positive contraction.  If the factorization approximates
the unit within `epsilon`, then

```text
norm(1-a_0-a_1)<=epsilon.
```

The positive element `a_0+a_1` is at most `(1+epsilon)1`.  Hence

```text
h_i=(1+epsilon)^(-1)a_i
```

is a subunital pair with

```text
norm(1-h_0-h_1)<=eta,
eta=2epsilon/(1+epsilon).                             (RTP6)
```

Do this for the second factorization as well.  Orthogonality of
corresponding return-colour ranges gives `a_i b_i=0`, hence the scaled
pairs satisfy (RTO1) with error `eta`.  For `epsilon<1/15`, the spectral
argument applies.  Let `i` be the returned unit piece with

```text
norm(a_i)<=(1+epsilon)alpha(eta).
```

The composition `T_i=phi_i o psi_i:D->D` is c.p.c. and
`norm(T_i)=norm(T_i(1))=norm(a_i)`.  Therefore, for every contraction `a`
in the prescribed finite set,

```text
norm(a-phi_(1-i) psi_(1-i)(a))
 <= norm(a-phi psi(a))+norm(phi_i psi_i(a))
 <= epsilon+(1+epsilon)alpha(eta).                    (RTP7)
```

The surviving return map is c.p.c. order zero.  As
`epsilon+(1+epsilon)alpha(eta)`
tends to zero, (RTP7) supplies nuclear-dimension-zero approximations.
For separable C-star algebras, nuclear dimension zero is equivalent to AF.

For the scalar interval application, evaluate at a point `t` where two
cutoffs `g` and `g'` are positive.  If localized return maps from the two
frames share a global order-zero colour, their support product is

```text
g(t)g'(t) h_i k_i=0.
```

The scalar coefficient is nonzero, so `h_i k_i=0`.  Relabel the second
frame according to the global-colour matching and apply the preceding
argument.  Here there are only two cases.  If the two local colours of one
frame were assigned the same global colour, their ranges would already be
orthogonal and that local approximation would be one-coloured.  Otherwise
each frame uses both global colours, so the claimed matching exists.  No
stationary identification or continuous choice of conjugating unitaries is
used.
