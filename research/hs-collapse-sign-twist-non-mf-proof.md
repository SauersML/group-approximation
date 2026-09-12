---
rg: 2
id: hs-collapse-sign-twist-non-mf-proof
kind: route
title: Cut the fresh sign corner and force the old collapse mark to have trace zero
target: hs-collapse-sign-twist-non-mf
requires: []
---

We prove all three assertions of `hs-collapse-sign-twist-non-mf` from the
printed hypotheses.

## 1. Algebraic construction and nontriviality of the fresh sign

Let `B=Gamma x C_2`, and write `z` for the generator of the second factor.
Because `w` is a nontrivial involution in `Gamma`,

```text
K=<w,z> <= B
```

is a Klein four group.  Define an automorphism `theta:K->K` by

```text
theta(w)=z w,
theta(z)=z.                                                   (P1)
```

The group in `(HST4)` is exactly the HNN extension

```text
HNN(B,K,theta)=<B,a | a k a^-1=theta(k), k in K>.              (P2)
```

Indeed it is enough to impose `(P1)` on the two generators `w,z` of `K`;
the relation for `z` is `[z,a]=1`.  Britton's lemma embeds the base `B` in
this HNN extension.  Therefore the original copy of `Gamma` embeds, `z` has
order exactly two, and in particular

```text
z!=1 in Gamma^tw.                                             (P3)
```

The displayed presentation is finite because `S` and `R` are finite.

## 2. Assume a norm-corona representation keeps `z` alive

Let

```text
Q = product_n M_(d_n)(C) / directSum_n M_(d_n)(C)
```

and suppose

```text
Theta:Gamma^tw -> U(Q)                                       (P4)
```

is a homomorphism with `Theta(z)!=1`.  Put `Z=Theta(z)`.  Since `z` is a
central involution, `Z` is a central self-adjoint unitary relative to
`Theta(Gamma^tw)`, and

```text
q=(1-Z)/2                                                     (P5)
```

is a nonzero projection commuting with the whole image.  On the `q` corner,

```text
qZ=-q.                                                        (P6)
```

Choose unitary coordinate lifts of the finitely many generator images.  Lift
`q` to projections `q_n in M_(d_n)(C)`: start from a self-adjoint lift of
`q`, whose idempotence defect tends to zero in operator norm, and apply the
spectral cut at `1/2`.  Because `q!=0`, `q_n` is nonzero for infinitely many
`n`; restrict to those coordinates and put

```text
r_n=rank(q_n)>0.                                              (P7)
```

Centrality of `q` in the quotient gives, for every printed generator `g`,

```text
||[q_n,V_(g,n)]||_op -> 0,                                   (P8)
```

where `V_(g,n)` is the chosen unitary lift of `Theta(g)`.

## 3. Polar-correct the corner to an ordinary matrix microstate

For every generator `g` other than `z`, the compression

```text
q_n V_(g,n) q_n
```

is asymptotically unitary in the corner `q_n M_(d_n) q_n`.  For example,
using `(P8)`,

```text
||(qVq)*(qVq)-q||_op <= 2||[q,V]||_op -> 0.                  (P9)
```

Thus polar decomposition gives a unitary

```text
U_(g,n) in U(q_n C^(d_n)) ~= U(r_n)                           (P10)
```

with

```text
||U_(g,n)-q_nV_(g,n)q_n||_op ->0.                            (P11)
```

For the sign generator set, exactly,

```text
U_(z,n)=-I_(r_n).                                             (P12)
```

This differs by `o(1)` in operator norm from the compressed lift of `Z`
because `(P6)` holds in the quotient.

Every defining relator of `Gamma^tw` is a fixed word.  The original lift
sequences evaluate those relators to `I+o_op(1)`, compression changes a fixed
product by `o_op(1)` using `(P8)`, and the finitely many polar corrections
change it by another `o_op(1)`.  Hence the corner tuples form an
operator-norm asymptotic representation of the printed presentation.  In
particular, on the original `Gamma` generators,

```text
max_(r in R) ||r(U_n)-I||_op ->0.                             (P13)
```

Since normalized Hilbert--Schmidt norm is at most operator norm, `(P13)` also
gives

```text
max_(r in R) ||r(U_n)-I||_(2,r_n) ->0.                        (P14)
```

For all sufficiently large `n`, `(P14)` is below the fixed `delta` in
`(HST1)`.  Writing

```text
W_n=w(U_n),                                                   (P15)
```

the assumed HS-collapse therefore gives

```text
||W_n-I||_(2,r_n) <= alpha.                                   (P16)
```

## 4. The sign-twist relation forces zero trace on the same corner

Let

```text
A_n=U_(a,n).
```

The defining relation `a w a^-1=z w`, together with `(P12)`, gives

```text
||A_n W_n A_n* + W_n||_op ->0.                               (P17)
```

Let `tr_n` denote the normalized trace on the `r_n`-dimensional corner.
Because trace is invariant under unitary conjugation,

```text
2 |tr_n(W_n)|
 = |tr_n(A_n W_n A_n*) + tr_n(W_n)|
 <= ||A_n W_n A_n* + W_n||_op
 ->0.                                                         (P18)
```

Thus `tr_n(W_n)->0`.  Since every `W_n` is unitary,

```text
||W_n-I||_(2,r_n)^2
 = tr_n((W_n-I)*(W_n-I))
 = 2-2 Re tr_n(W_n)
 ->2.                                                         (P19)
```

Therefore

```text
||W_n-I||_(2,r_n) -> sqrt(2),                                 (P20)
```

which contradicts the uniform bound `(P16)` because `alpha<sqrt(2)`.

The assumption `Theta(z)!=1` was impossible.  Hence every homomorphism
`Gamma^tw->U(Q)` kills `z`.

## 5. Non-MF endpoint

By `(P3)`, `z` is nontrivial in `Gamma^tw`.  By the preceding argument, `z`
lies in the kernel of every homomorphism from `Gamma^tw` to the unitary group
of every norm matrix corona.  No such homomorphism can therefore be
injective.  This is exactly failure of the CDE/operator-MF property.

No property `(T)`, asymptotic-commutant theorem, or previously constructed
non-MF group enters the proof.  The only analytic input supplied by the
source group is the finite-dimensional HS-collapse estimate `(HST3)`; the new
HNN relation turns that trace bias into an operator-norm corona obstruction.
