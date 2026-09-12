---
rg: 2
id: ore-heisenberg-telescope-coset-action-proof
kind: route
title: Use common left multiples in the positive Heisenberg compressor monoid
target: heisenberg-kun-thom-slice-is-relatively-embeddable
requires:
  - monomial-ascending-hnn-coset-action-sofic
  - ascending-hnn-action-iff-iterated-cosets
  - sofic-coset-action-makes-amalgam-double-sofic
---

Write `a=(1,A)`, `b=(1,B)`, and `c=(1,C)`.  In the external matrix
group,

```text
c=[a,b],       c central,       a b=c b a.                    (OHT1)
```

Thus `Q=<a,b>` is the integral Heisenberg group.

## The positive monoid is left Ore

Include the generated positive element `c` and put `S=<a,b,c>_+`.
Relation (OHT1) gives the unique normal form

```text
s=c^rho b^q a^p,       p,q,rho in N.
```

Encode it by `(p,q,rho)`.  Multiplication is

```text
(p,q,rho)(p',q',rho')
 =(p+p',q+q',rho+rho'+p q').                                 (OHT2)
```

Given `s=(p,q,rho)` and `t=(p',q',rho')`, choose
`P>=max(p,p')` and `Q_0>=max(q,q')`.  A left multiplier of `s` with
first two coordinates `(P-p,Q_0-q)` produces central coordinate

```text
R+rho+(P-p)q,
```

and the analogous multiplier of `t` produces

```text
R'+rho'+(P-p')q'.
```

Choose a common integer `L` at least both fixed terms and take `R,R'` to
be the two nonnegative deficits from `L`.  The resulting elements
`u,v in S` satisfy

```text
u s=v t.                                                       (OHT3)
```

So `S` is left Ore.  It is cancellative because it is a submonoid of
`Q`, and its fraction group is `Q).  In particular every `q in Q` has
a form `q=d^(-1)e` with `d,e in S), and finitely many denominators in
`S` have one common left multiple.

## The Ore telescope

For `s in S`, set

```text
Gamma_s=s^(-1) Gamma s.
```

If `w=u s` is a left multiple, then

```text
Gamma_s subset Gamma_w
```

because `Gamma subset u^(-1)Gamma u`.  Hence (OHT3) makes

```text
N=union_(s in S) Gamma_s                                      (OHT4)
```

a directed union.

This is exactly the kernel part of `P`.  Indeed, if
`q=d^(-1)e in Q`, then

```text
q^(-1) Gamma q=e^(-1)d Gamma d^(-1)e subset e^(-1)Gamma e.
```

The same fraction calculation shows that conjugation by every `q in Q`
permutes the union (OHT4).  Projection to the external factor and the
canonical section therefore give

```text
P=N rtimes Q.                                                  (OHT5)
```

Every `s in S` is a nonnegative unimodular matrix, so it is a positive
monomial compressor and

```text
s Gamma s^(-1)=EL_r(k[s N^d]).
```

Exactly as in `monomial-ascending-hnn-coset-action-sofic`, a monomial
outside `s N^d` survives in a sufficiently deep finite quotient
`k[x_1,...,x_d]/(x_1^M,...,x_d^M)`.  Suslin stability over the polynomial
ring `k[s N^d]` then shows `s Gamma s^(-1)` is separable in `Gamma).

## One level captures every finite action window

Let `X=P/Gamma`, and fix finite `F subset N` and `E subset X`.  Write

```text
x=n_x q_x Gamma,       n_x in N, q_x in Q.
```

Choose levels containing `F` and all `n_x`.  Write
`q_x=d_x^(-1)e_x` with `d_x,e_x in S).  By (OHT3), there is one
`s in S` which is a common left multiple of all the chosen level indices
and all `d_x).  Then

```text
F subset Gamma_s,       n_x in Gamma_s,       t_x=s q_x in S. (OHT6)
```

Conjugate `Gamma_s` back to `Gamma).  For

```text
g=s^(-1) gamma s,       n_x=s^(-1)h_x s,
```

the stabilizer calculation is

```text
g x=x
iff q_x^(-1)n_x^(-1)g n_x q_x in Gamma
iff t_x^(-1)h_x^(-1)gamma h_x t_x in Gamma
iff h_x^(-1)gamma h_x in t_x Gamma t_x^(-1).                 (OHT7)
```

The last subgroup is a conjugate of a separable positive monomial image.
Thus every `Gamma_s`-orbit meeting `E` has an exact finite Schreier model.
The disjoint union of the finitely many relevant orbit models handles the
prescribed window.  Since every finite `N`-window admits (OHT6), the action
`N action X` is sofic.

## Adjoin the Heisenberg quotient cyclically

Use the chain

```text
N
normal N rtimes <c>
normal N rtimes <c,a>
normal N rtimes Q=P.                                          (OHT8)
```

The successive quotients are infinite cyclic.  The last normality follows
from

```text
b c b^(-1)=c,       b a b^(-1)=c^(-1)a.
```

Apply the cyclic-extension permanence theorem for sofic actions three times
to (OHT8).  It follows that `P action P/Gamma` is sofic.

The Kun--Thom ambient group is residually finite, hence its subgroup `P` is
sofic.  The theorem
`sofic-coset-action-makes-amalgam-double-sofic` now makes
`P *_Gamma P` sofic.  Finally `a^k notin Gamma` for `k!=0), as seen in
the external Heisenberg quotient.  Its Haar-relative-unitary conclusion gives
`L(Gamma) subset L(P)` relatively embeddable over the scalars.
