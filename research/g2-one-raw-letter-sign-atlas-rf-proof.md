---
rg: 2
id: g2-one-raw-letter-sign-atlas-rf-proof
kind: route
title: Give triangular and finite-truncation models for the two one-letter envelopes
target: g2-one-raw-letter-sign-atlas-is-residually-finite
requires:
  - g2-conditioned-jacobson-sign-envelope-is-finite
  - qutrit-one-raw-letter-head-router-is-residually-finite
  - jacobson-sign-polar-ranks-are-five-over-72-and-one-over-16
---

## 1. The raw negative letter

For

```text
B_-=F_2<q,T>,                   q^2=q,       Tq=0,
```

every word reduces to the span of

```text
1,              T^n (n>=1),              qT^n (n>=0). (GRA4)
```

The faithful polynomial-matrix embedding is

```text
q |-> [[1,0],[0,0]],          T |-> [[0,1],[0,x]].
                                                               (GRA5)
```

Indeed the images of the normal words are

```text
T^n  |-> [[0,x^(n-1)],[0,x^n]],
qT^n |-> [[0,x^(n-1)],[0,0]]              for n>=1,
```

together with `1,q`. They are linearly independent. Reduction modulo
`x^N` separates every prescribed nonzero element, so `B_-` is
residually finite.

The coefficients `q,a=qT,T` of `H,A_0,W,U` all lie in `B_-`.
The matrices `C` and `g_2` are scalar. This proves the first containment
in `(GRA3)`.

## 2. The asymmetric raw positive letter

The sign envelope contains `a=qT` rather than a raw negative letter.
Set

```text
B_+=F_2<S,q,a> <= J.
```

In the faithful half-line Jacobson model,

```text
S e_i=e_(i+1),            q=E_(0,0),          a=E_(0,1).
```

The defining reductions inherited from `J` are

```text
q^2=q,       qS=0,        qa=a,        aq=0,
a^2=0,       aS=q.                                      (GRA6)
```

They reduce every word to the span of

```text
S^n                         (n>=0),
S^n q,       S^n a          (n>=0).                     (GRA7)
```

These normal words are linearly independent. A nonzero polynomial in
`S` has infinite-rank tail action and cannot cancel the finite matrix
units

```text
S^nq=E_(n,0),                  S^na=E_(n,1).
```

The matrix units themselves are distinct. Consequently `(GRA6)` is a
presentation of the concrete algebra `B_+`.

For `N>=1`, let `S_N` be the nilpotent shift on the
`(N+1)`-dimensional space with basis `e_0,...,e_N`, and put

```text
q_N=E_(0,0),                  a_N=E_(0,1).
```

These finite matrices satisfy every relation in `(GRA6)`, so the
assignment

```text
S |-> S_N,             q |-> q_N,             a |-> a_N
```

defines a homomorphism from `B_+` to `M_(N+1)(F_2)`. Given a nonzero
normal form `(GRA7)`, choose `N` larger than every occurring exponent.
If its polynomial part is nonzero, apply it to a basis vector
`e_k` with `k>=2` and enough room before the truncation boundary;
the distinct shifts cannot cancel. If the polynomial part is zero, the
distinct first- and second-column matrix units remain distinct. Thus
some finite truncation separates the element, proving that `B_+` is
residually finite.

The coefficients `q,a,S` of `H,A_0,W,V` lie in `B_+`, while `C,g_2`
are scalar. This proves the second containment in `(GRA3)`.

## 3. Residual finiteness of the matrix groups

Let `B` be either `B_-` or `B_+`. If
`M in GL_28(B)` is nonidentity, one entry of `M-I` is a nonzero element
`b` of `B`. Choose a finite-ring quotient of `B` which does not kill
`b`. Entrywise reduction maps `M` to a nonidentity invertible matrix
over that finite ring. Hence `GL_28(B)`, and therefore each subgroup in
`(GRA2)`, is residually finite.

Both groups in `(GRA2)` are finitely generated. Enumerate their
nonidentity elements and intersect the first `n` separating finite-index
normal subgroups. The resulting descending finite quotients have trivial
kernel intersection. Their regular traces converge pointwise to the
canonical group trace. In particular their permutation matrices are
normalized-Hilbert--Schmidt microstates.

This conclusion includes every placement and every power of `g_2`.
The coefficient ring is unchanged by scalar multiplication or scalar
conjugation; word length cannot introduce the missing opposite raw
orientation.

## 4. The exact one-step sign atlas

The commuting sign roots satisfy

```text
UHU=HA_0,              [U,A_0]=[U,W]=1,
VA_0V=A_0W,            [V,H]=[V,W]=1.                  (GRA8)
```

For `G=G_(sigma,tau)`, exactly the calculation in
`(QBH10)--(QBH11)` gives

```text
(GUG)^2=G if sigma=+,       (GUG)^2=0 if sigma=-,
(GVG)^2=G if tau=+,         (GVG)^2=0 if tau=-.         (GRA9)
```

These self-adjoint compressions therefore have full support `G` in the
surviving rows and zero support in the other rows. After the qutrit
source cut `R`, their source polar ranks are precisely the already
computed ranks of `G R`:

```text
5/72 for (+,+),                    1/16 for every nontrivial sign.
                                                               (GRA10)
```

Multiplying `GUGR` or `GVGR` on the left by `g_2^j` is unitary and
does not change `(GRA10)`. Other placements of `g_2` need not preserve
this literal sign projection, but `Section 3` places every such word in
the same residually finite group. Thus no placement can be the source
of a genuine nonhyperlinearity obstruction while only one raw orientation
is present.

The sharp next coefficient threshold is a same-word occurrence of both
`T` and `S`. That is exactly where the two separate residual-finiteness
proofs stop.
