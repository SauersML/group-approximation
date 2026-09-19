---
rg: 2
id: kl-test-word-conjunction-fence-proof
kind: route
title: Use stable-letter degree, equivariance of group words, and a cyclic HNN countermodel
target: kl-test-word-conjunction-fence
requires:
  - leavitt-omega-has-an-explicit-distorted-target
  - leavitt-corners-cannot-compress-external-variable
---

Put `F=G*<t>` and let `deg_t:F -> Z` kill `G` and send `t` to `1`.  Both
transport relators

```text
E_a=t^(-1)atc^(-1),       E_r=t^(-1)rtp^(-1)            (TW1)
```

have degree zero.  Hence

```text
<<E_a,E_r>>_F  <=  ker(deg_t).                           (TW2)
```

Every word which follows from the two transports belongs to their normal
closure, so `(TW2)` proves that it has degree zero.  This remains true after
the incompatible transports collapse nontrivial coefficients: the quotient
by `(TW1)` still maps onto `Z` by stable-letter degree.  Consequently no
nonsingular word can be a consequence of the transports, and in particular
no nonsingular word can be an equivalent one-relator encoding of them.  This
does not rule out a KL word which *implies* the transports while imposing an
additional degree-carrying relation; it proves that such a word must be a
strictly stronger, self-referential construction rather than a conjunction
compiler.

Now let `V(X,Y)` be any word in the coefficient-free free group `F(X,Y)`.
Evaluation of group words commutes with simultaneous conjugation, so

```text
V(t^(-1)at,t^(-1)rt)=t^(-1)V(a,r)t.                    (TW3)
```

Thus equality of the source and target test-word values gives only

```text
H_V=<G,t | t^(-1)ut=v>,
u=V(a,r), v=V(c,p).                                    (TW4)
```

If `u |-> v` defines an isomorphism `<u> -> <v>` (equivalently, `u` and `v`
have the same order), `(TW4)` is an HNN extension of `G` along two cyclic
subgroups.  Britton's lemma makes the canonical map `G -> H_V` injective.
It follows in particular that `(TW4)` cannot imply both equations `(TW1)`:
those equations would transport the identity

```text
Omega(a,r)=1
```

to the explicitly nonidentity coefficient

```text
Omega(c,p)=x_15(s_0^2) != 1,
```

contradicting injectivity.  If the orders of `u` and `v` differ, `(TW4)` is
not this HNN extension, but its only information is still the single cyclic
transport and it remains singular.  An order-mismatch collapse is not a
two-entry test-word theorem and cannot itself be a nonsingular KL relator.

For completeness, no alternative coefficient-free detector has a universal
identity fiber.  Given `W(X,Y)`, let `(alpha,beta)` be its exponent-sum vector.
In a cyclic group `C_l=<g>` of prime order, evaluation at `(g^i,g^j)` is

```text
W(g^i,g^j)=g^(alpha i+beta j).                         (TW5)
```

The homogeneous linear map `F_l^2 -> F_l` in `(TW5)` has a nonzero kernel
(and is the zero map if both exponent sums vanish modulo `l`).  Hence some
`(g^i,g^j)!=(1,1)` satisfies `W=1`.  This includes products and iterated
commutators of the two formal errors.  Free-group `C`-test-word theorems do
not evade the argument: their rigidity hypotheses concern tuples which
remain noncyclic inside a fixed free group, whereas the KL quotient ranges
over arbitrary overgroups and `(TW4)` is an explicit countermodel.
