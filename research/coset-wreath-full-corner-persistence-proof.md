---
rg: 2
id: coset-wreath-full-corner-persistence-proof
kind: route
title: Prove ICC and preserve the Bernoulli wall under full commutant compression
target: coset-wreath-wall-survives-full-commutant-corners
requires:
  - kt-finitary-action-is-outer-mod-scalar-core
  - coset-bernoulli-ce-refutes-relative-commutant-collapse
---

## Step 1: the generalized wreath is ICC

Write the lamp group `A` additively.  An element of `W` is a pair `(b,g)`
with multiplication

~~~text
(b,g)(c,h)=(b+g.c,gh).                                  (BCP1)
~~~

Suppose first that `g!=1`.  By hypothesis there are infinitely many
`x in X` with `gx!=x`.  If `delta_x` is the lamp supported at `x`, then

~~~text
(delta_x,1)(b,g)(delta_x,1)^(-1)
  =(b+delta_x+delta_(gx),g).                            (BCP2)
~~~

The two-point supports `{x,gx}` take infinitely many values: one such
unordered support has at most two preimages under `x|->{x,gx}`.  Hence
`(b,g)` has infinitely many conjugates.

Now let `g=1` and `0!=b in A`.  Its support `F` is finite and nonempty.
Conjugation by `(0,h)` sends `F` to `hF`.  If the orbit of `F` were finite,
the union of that orbit would be a finite nonempty `G`-invariant subset of
`X`.  Transitivity would make that union all of `X`, contrary to the
infinitude of `X`.  Thus `(b,1)` also has infinitely many conjugates.

Every nonidentity element of `W` therefore has an infinite conjugacy class.
Since `W` is countable, `N=L(W)` is a `II_1` factor.

## Step 2: a full multiplicity corner preserves the canonical trace

Identify `N` with its image under `Theta`.  Let `E_N:M->N` be the
trace-preserving conditional expectation.  If `e in N' cap M` is a
projection, bimodularity gives, for every `x in N`,

~~~text
x E_N(e)=E_N(xe)=E_N(ex)=E_N(e)x.                       (BCP3)
~~~

Thus `E_N(e)` lies in `Z(N)=C1`.  Taking traces determines the scalar:

~~~text
E_N(e)=tau(e)1.                                         (BCP4)
~~~

Because `e` commutes with `N`, the map `Theta_e(x)=eTheta(x)` is a unital
star homomorphism from `N` to the corner `eMe`.  Equations `(BCP3)` and
`(BCP4)` give

~~~text
tau_e(Theta_e(x))
 =tau(eTheta(x))/tau(e)
 =tau(E_N(e)Theta(x))/tau(e)
 =tau_N(x).                                             (BCP5)
~~~

It is therefore trace preserving and, because the canonical factor trace is
faithful, injective.

This is the point at which factoriality matters.  For a nonfactor, a
relative-commutant corner can select a different central trace.  Here there
is only one normalized trace to select.

## Step 3: the balanced wall is unchanged

Let `a_x` be the canonical order-two lamp at `x` and put
`p_x=(1+a_x)/2`.  The group trace gives, for distinct points
`x_1,...,x_k`,

~~~text
tau(a_(x_1)...a_(x_k))=0,
tau(p_(x_1)...p_(x_k))=2^(-k).                          (BCP6)
~~~

Indeed every nonempty product of distinct lamps is a nonidentity element of
the direct sum.  These are exactly the centered Walsh moments and the
Bernoulli Boolean moments.

If `x_0` has stabilizer `Lambda`, then `a_(x_0)` and `p_(x_0)` commute
with every canonical `u_lambda`.  For `y=gamma x_0!=x_0`,

~~~text
u_gamma p_(x_0) u_gamma^*=p_y,
tau(p_(x_0))=tau(p_y)=1/2,
tau(p_(x_0)p_y)=1/4.                                    (BCP7)
~~~

Since the projections commute,

~~~text
||p_y-p_(x_0)||_2^2
 =tau(p_y)+tau(p_(x_0))-2tau(p_(x_0)p_y)
 =1/2.                                                   (BCP8)
~~~

Apply the trace-preserving map `Theta_e` from Step 2.  It preserves
`(BCP6)`--`(BCP8)` verbatim, proves all identities in `(BWC5)`, and shows
that no nonzero full multiplicity corner changes either the balance or the
mover energy.

## Step 4: the apparently weaker corner hypothesis is already full

Let `sigma(g)=Theta(u_g)` and `p=Theta(p_(x_0))`.  Suppose a projection
`e` commutes with every `sigma(g)` and with `p`.  Transitivity says every
lamp projection has the form

~~~text
p_x=sigma(g)p sigma(g)^*                                (BCP9)
~~~

for some `g`.  Hence `e` commutes with every `p_x`.  The orbit projections
generate the whole Bernoulli lamp algebra, while that algebra together with
`sigma(G)` generates `Theta(L(W))`.  Therefore

~~~text
e in Theta(L(W))' cap M.                                (BCP10)
~~~

Step 2 applies.  Thus an actor-multiplicity corner which still supports the
base projection is not a weaker escape: it is a full multiplicity corner and
retains the canonical trace.

## Step 5: the Kun--Thom q=2 specialization

For the pinned Kun--Thom pair over `F_2`,

~~~text
Lambda=t Gamma t^(-1) subset Gamma subset G.            (BCP11)
~~~

The map

~~~text
G/Lambda -> G/Gamma,          gLambda |-> gGamma        (BCP12)
~~~

is a surjective `G`-map.  By
`kt-finitary-action-is-outer-mod-scalar-core`, at `q=2` every nonidentity
`g in G` moves infinitely many points of `G/Gamma`.  For each moved point
downstairs, every chosen lift in `G/Lambda` is also moved.  Thus every
nonidentity `g` moves infinitely many points of `G/Lambda`, and Step 1
applies to

~~~text
W=(direct_sum_(G/Lambda) C_2) semidirect G.             (BCP13)
~~~

The base coset has stabilizer `Lambda`, and every
`gamma in Gamma minus Lambda` moves it.  Therefore any
trace-preserving matrix-ultraproduct embedding of `L(W)` contains the exact
balanced FDT7 wall `(BCP7)`--`(BCP8)` in every nonzero full multiplicity
corner.

This proves corner persistence only.  It neither constructs such an
embedding nor rules one out.  Hyperlinearity of `W`, FDT7, and (CCR) remain
open.
