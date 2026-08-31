---
rg: 2
id: rectangular-commutant-and-qutrit-bimodule-absorber-proof
kind: route
title: Put the covariant cokernel in the commutant and count the qutrit regular bimodule
target: finite-same-trace-tags-have-a-commutant-or-absorber-dichotomy
requires:
  - finite-packet-trace-authentication-is-internal-equivalence
  - jacobson-sign-polar-ranks-are-five-over-72-and-one-over-16
  - rectangular-safe-covariance-has-a-positive-head-absorber
---

## Covariance puts the head in the commutant

For `a in A`, the intertwining equation and its adjoint are

```text
pi_T(a)S=S pi_S(a),
S^*pi_T(a)=pi_S(a)S^*.
```

Therefore

```text
pi_T(a)SS^*
 =S pi_S(a)S^*
 =SS^*pi_T(a).
```

Subtracting from `pi_T(a)` proves `(STA1)`.

Write the represented finite-dimensional algebra in standard form:

```text
pi_T(A)=direct-sum_i (M_(d_i)(C) tensor I_(m_i)).
```

Its commutant is

```text
pi_T(A)'=direct-sum_i (I_(d_i) tensor M_(m_i)(C)).
```

If `Q=pi_T(p)`, then in the `i`th block it has both forms

```text
p_i tensor I_(m_i) = I_(d_i) tensor Q_i.                 (RCQ1)
```

The intersection of the two tensor factors consists of scalars. Since
both sides are projections, `p_i` is zero or the identity on every
represented simple block. This proves the literal-authentication half of
`(STA2)`.

If only equal rank is prescribed, choose orthonormal bases of the two
ranges and of the two kernels. The basis bijections assemble to a unitary
`W` with

```text
WQW^*=pi_T(p).                                           (RCQ2)
```

No covariance of `W` follows from `(RCQ2)`.

For completeness, let

```text
A=direct-sum_i M_(d_i)(C),       p=(p_i),       r=(r_i).
```

A representation with multiplicity vector `(m_i)` has

```text
tr_pi(p)
 =sum_i m_i rank(p_i) / sum_i m_i d_i.                   (RCQ3)
```

If `tr_pi(p)=tr_pi(r)` for every representation, use the irreducible
representation supported on one block at a time. It gives
`rank(p_i)=rank(r_i)` for every `i`. Choose a blockwise partial
isometry `v_i` between them and put `v=direct-sum_i v_i`. Then

```text
v^*v=p,                         vv^*=r.                  (RCQ4)
```

If one block has unequal ranks, repeating that irreducible block gives an
exact finite packet representation with the same fixed normalized
mismatch. This is the absorber side of `(STA2)`.

## The abelian qutrit 17-to-18 model

Let

```text
B=<H> times C,                  |B|=2*9=18.
```

The head `H` commutes with the qutrit torus `C`. Hence, for any
qutrit character atom `e_b`,

```text
q_b=E e_b,                     E=(1-H)/2
```

is one of the eighteen minimal central character projections of
`C[B]`.

Let `H_T=ell^2(B)` with its regular representation. In its Fourier
basis there is one line `L_chi` for every character `chi` of `B`.
The range of `q_b` is one of those lines. Set

```text
H_S=direct-sum_(chi != chi_b) L_chi
```

and let `S:H_S->H_T` be the coordinate inclusion. Both spaces are
`B`-invariant and `S` is a `B`-intertwiner. With `T=S^*` and
`Q=q_b`,

```text
TS=I_(H_S),             ST=I_(H_T)-Q,
QS=0,                   TQ=0.                            (RCQ5)
```

The dimensions are seventeen and eighteen, proving `(STA3)`.

This rectangular operator can be encoded by finite group unitaries.
On `K=H_T direct-sum H_S`, put

```text
z=[ I  0 ],                  a=[ Q  S ].
  [ 0 -I ]                     [ T  0 ]
```

Using `(RCQ5)`,

```text
a^2=z^2=I,
(az)^2=diag(2Q-I,-I),
(az)^4=I.                                                (RCQ6)
```

Both `a` and `z` commute with the diagonal `B`-representation,
because `Q` commutes with `B` and `S` intertwines it. Thus
`<a,z>` is a quotient of `D_8`, and the whole image is a quotient of
`B times D_8`.

Let `p_T=(1+z)/2` and `p_S=(1-z)/2`. Direct block multiplication
gives

```text
p_T a p_T=Q,        p_T a p_S=S,
p_S a p_T=T,        p_S a p_S=0.                         (RCQ7)
```

So the positive head, its same-trace tag, and the rectangular occurrence
all belong to one exact finite group-algebra model. This is not merely a
dimension count.

## The full 288-element qutrit packet

Now take

```text
F_0=<C,H,C_1,W>
   isomorphic to C_2 times C_3 times (F_2^4 semidirect C_3).
```

The established Frobenius-block calculation gives

```text
|F_0|=288,                         tau_reg(q_b)=1/18.     (RCQ8)
```

Thus left or right multiplication by `q_b` on `ell^2(F_0)` has rank

```text
288/18=16.                                               (RCQ9)
```

Let `lambda` be left translation and let

```text
Q=R(q_b): xi |-> xi q_b
```

be right multiplication in the finite group algebra. Associativity gives

```text
Q lambda(g)=lambda(g)Q                  for every g in F_0. (RCQ10)
```

The range of `I-Q` is therefore left invariant. Take it as `H_S`,
take `H_T=ell^2(F_0)`, and again use the inclusion for `S`.
Equations `(RCQ5)--(RCQ7)` repeat verbatim, now with

```text
dim(H_T)=288,             dim(H_S)=288-16=272=16*17.     (RCQ11)
```

Moreover `a,z` commute with the diagonal left `F_0`-action, so this
model too has finite image, a quotient of `F_0 times D_8`.

It remains to distinguish equal trace from literal packet position.
Fix the negative `H`-character and the central `h`-character selected
by `q_b`. In each relevant three-dimensional representation induced
from a nonzero character orbit of `F_2^4`, the qutrit Fourier
projection has rank one. Hence

```text
rank(pi(q_b))=1                         in a 3-dimensional block. (RCQ12)
```

A central projection in an irreducible three-dimensional block has rank
zero or three, so `q_b` is not central in `C[F_0]`. Equivalently,
`L(q_b)` does not commute with the left regular image. It cannot be the
literal `Q` in a fully left-`F_0`-covariant occurrence by `(STA1)`.

Nevertheless `L(q_b)` and `R(q_b)` both have rank sixteen. Equation
`(RCQ2)` supplies a unitary router between them. If that router were
also a left-`F_0` intertwiner, it would conjugate one commutant
projection to another, contradicting the noncentrality of `L(q_b)`.
Thus the exact missing datum is not trace but a mixed covariance law for
the router. Such a law cannot come from the finite packet alone; it must
consume the raw Jacobson occurrence.
