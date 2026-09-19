---
rg: 2
id: leavitt-nielsen-collision-has-a-hidden-first-side-relation-proof
kind: route
title: Conjugate one Leavitt root twice through qp and retain the bridge syllables after Tietze elimination
target: leavitt-nielsen-collision-has-a-hidden-first-side-relation
requires:
  - leavitt-length-six-nielsen-collision-candidate
---

## The first corner subgroup is not the naive folded atlas

Keep the notation of the collision candidate and put

```text
r=qp,
a=x_12(s_0),
q=x_34(s_1)x_(11,12)(t_0).
```

The two first-relator corners adjacent through the repeated `a_0` give

```text
h_0h_1=(q_1a_0)(a_0p_1)=(qp)_1=r_1.                 (HR1)
```

Let `u=k_0=k_1=a_1` and `b=h_0h_1=r_1`.  Conjugating in one coefficient
copy gives

```text
r a r^(-1)=q (p a p^(-1))q
           =x_23(s_0)x_24(s_0s_1).                  (HR2)
```

Indeed `p a p^(-1)=x_23(s_0)`.  The far
`x_(11,12)(t_0)` factor commutes with this root, while conjugation by
`x_34(s_1)` adds `x_24(s_0s_1)` by the Steinberg relation.  Conjugating once
more shifts the two roots and the two factors of `q` then commute with both:

```text
r^2 a r^(-2)=x_34(s_0)x_35(s_0s_1).                 (HR3)
```

Both roots in `(HR3)` commute with `x_12(s_0)`.  Hence

```text
Omega=[a,r^2 a r^(-2)]=1,                            (HR4)
```

and therefore `[u,b^2u b^(-2)]=1` in the actual first corner subgroup.
In the formal group `<u,b | u^2=1>=C_2*Z`, the two involutions `u` and
`b^2ub^(-2)` lie in distinct conjugates of the `C_2` free factor.  Their
commutator is a nonempty cyclically reduced word.  Thus the first corner map
has a kernel even after the literal gate collision has been folded.

The artifact verifies `(HR2)--(HR4)` on the faithful standard Leavitt module.
It partitions an arbitrary infinite binary word into exactly the finitely many
initial cylinders inspected by the deletion operators and keeps the remaining
tail opaque.  This is a symbolic exhaustive check, not a finite-word or
finite-dimensional truncation.

## What happens on the Tietze side

Write the paired relators cyclically as

```text
x z h z y z^(-1)=1,
u z u z k z^(-1)=1,                                  (HR5)
```

where

```text
x=h_0=q_1a_0,  h=h_1=a_0p_1,  y=h_2=e_0,
u=a_1,         k=k_2=p_0e_1q_0.
```

Put `s=z^(-1)`.  Direct solution of `(HR5)` for the two bridge corners gives

```text
h=s x^(-1)s^(-1)y^(-1)s,
k=s u s u s^(-1).                                    (HR6)
```

The repeated gate causes no cancellation in the second formula.  For
example, two equal `k` letters reduce only to

```text
k^2=s u s^2 u s^(-1),                                (HR7)
```

which is nontrivial in

```text
L=(<x>*C_2(y)*C_2(u))*<s>.
```

More generally, the formal folded corner group

```text
Q_form=(<x>*C_2(y)*C_2(u))*F(h,k)
```

maps injectively to `L` under `(HR6)`.  To see this, separate a reduced
`Q_form` word into base-group syllables and maximal `F(h,k)` blocks.  A
nontrivial base syllable is bracketed by nonzero `s`-syllables.  Inside a
free block every allowed join either leaves a nonzero power of `s`, exposes
one of `x^(±1)u` or `ux^(±1)`, or joins equal-sign powers of `k` as
in `(HR7)`.  None vanishes; the excluded joins are precisely inverse letter
pairs.  Thus the reduced `L` normal form is nonempty.

This formal injection does not prove coefficient injectivity, because
`(HR4)` shows that `Q_form` does not inject into the actual coefficient free
product.

## The hidden relation is not yet an outer boundary

Let

```text
B=xh=x s x^(-1)s^(-1)y^(-1)s                       (HR8)
```

be the Tietze image of `b=h_0h_1`.  Substitution into `(HR4)` gives

```text
Psi(Omega)=[u,B^2uB^(-2)].                           (HR9)
```

Exact free-product reduction in `L` leaves 49 alternating syllables, of
which 24 are nonzero `s`-syllables.  In particular `(HR9)` is not a word in
the coefficient base `<x>*C_2(y)*C_2(u)`.

This distinction is essential.  `Omega` is already the identity in the
coefficient group, whereas a KL violation requires a **nonidentity**
coefficient word which becomes trivial after the relative relators are
imposed.  Equations `(HR4)` and `(HR9)` provide a legitimate new internal
coefficient face for a bounded picture audit, but no outer coefficient
boundary.  A composite picture using this face and further exact coefficient
relations is still required.  Calling the collided word a KL violation, or
its Leavitt unit group nonhyperlinear, remains unjustified at this stage.

There is a precise algebraic test for that composite picture.  Let

```text
phi:Q_form -> C=G_0*G_1,       psi:Q_form -> L
```

be the first-corner and Tietze maps, and put `N=ker(phi)`.  On the corner
subgroup, a coefficient kernel is exactly a word

```text
w in psi^(-1)(<<psi(N)>>_L) \ N.                     (HR10)
```

Indeed `phi(w)` is then nonidentity, while a product of conjugates of
`psi(N)` is precisely a relative picture proving that its image dies.  For
the paired reduction of the original one-copy equation this is only a KL
certificate when `phi(w)` lies nontrivially in one of the factors `G_0` or
`G_1` (or when the same conjugate product explicitly yields such a one-factor
consequence).  A merely mixed nonidentity word of `G_0*G_1` detects failure
of the stronger paired embedding but does not by itself refute injectivity of
the original coefficient copy.

Thus the missing first test is strict failure of the congruence-extension
identity

```text
<<psi(N)>>_L intersect psi(Q_form) = psi(N).          (HR11)
```

The relation `Omega` proves only that `N` is nonzero.  It does not supply a
word in the strict difference `(HR10)`.  Nor can all first-side relations be
dismissed by claiming that `psi` splits: the free part of the abelianization
of `Q_form` has rank three, represented by `x,h,k`, while that of `L` has rank
two, represented by `x,s`; hence no retraction `L -> Q_form` can exist.

There are nevertheless three elementary retractions which fence off the
most tempting overclaim from `Omega` alone.  The quotient
`L/<<Psi(Omega)>>` maps onto `<x>`, `C_2(y)`, and `C_2(u)` by retaining the
named generator and killing `s` and all other base generators.  In each case
`B` becomes either `1` or an element commuting with the retained generator,
so `(HR9)` maps to `1`.  Thus the single hidden face does not kill any of the
visible base generators `x,y,u`.  These small retractions still do not prove
that either complete coefficient factor `G_i` embeds after all actual corner
relations are imposed.
