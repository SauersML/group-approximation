---
rg: 2
id: coset-wreath-wall-survives-full-commutant-corners
kind: claim
title: The coset-wreath balanced wall survives every full multiplicity corner
distinct_from:
  coset-bernoulli-ce-refutes-relative-commutant-collapse: that identifies Connes embeddability of a generalized Bernoulli crossed product as a conditional commutant refuter; this proves ICC and exact persistence of the refuting projection through every full relative-commutant corner.
  fdt7-is-balanced-bernoulli-projection-transfer: that turns an arbitrary pointed unitary FDT7 witness into a balanced projection and identifies the Bernoulli profile; this uses the entire canonical coset-wreath trace and shows multiplicity compression cannot dilute that profile.
  fct8-left-lift-and-rotated-defect-firewall: that studies rank ascent by left multiplication and shows the returned range is not pointwise fixed; this performs no adjoint ascent and instead uses factorial trace uniqueness in the original embedding.
  kt-finitary-action-is-outer-mod-scalar-core: that computes the infinite-support property of the Kun--Thom action on G/Gamma; this transports it to G/Lambda and uses it to prove the corresponding coset wreath is ICC.
artifacts:
  - research/kt-centralizer-normalization-hs.md
---

**ESTABLISHED CORNER THEOREM; HYPERLINEARITY STILL OPEN.**  Let `G` act
transitively on an infinite set `X`, and suppose every nonidentity element of
`G` moves infinitely many points of `X`.  Put

~~~text
A=direct_sum_X C_2,             W=A semidirect G.        (BWC1)
~~~

Then `W` is ICC, so `L(W)` is a `II_1` factor.

Let `Theta:L(W)->M` be a trace-preserving embedding into a finite tracial von
Neumann algebra, and let

~~~text
0!=e=e^2=e^* in Theta(L(W))' cap M.                     (BWC2)
~~~

With normalized corner trace `tau_e(y)=tau(y)/tau(e)`, the map

~~~text
Theta_e(x)=e Theta(x):L(W)->eMe                          (BWC3)
~~~

is again a trace-preserving embedding.  If
`M=product_omega M_(d_n)`, then `e` has projection lifts
`e_n in M_(d_n)` with

~~~text
rank(e_n)/d_n -> tau(e)>0,                              (BWC3b)
~~~

and `eMe`, with its normalized corner trace, is the tracial matrix
ultraproduct `product_omega M_(rank(e_n))`.  Thus the operation stays
inside the hyperlinear approximation class and uses no rank ascent.

Fix `x_0 in X`, let `Lambda=Stab_G(x_0)`, and choose
`gamma in G` with `gamma x_0!=x_0`.  If `a_x` is the order-two lamp at
`x` and

~~~text
p=(1+a_(x_0))/2,             p_e=e Theta(p),             (BWC4)
~~~

then in the original algebra and in every corner `(BWC2)` one has exactly

~~~text
tau_e(p_e)=1/2,
[e Theta(lambda),p_e]=0                  for lambda in Lambda,
||e Theta(gamma p gamma^(-1)-p)||_(2,e)^2=1/2.          (BWC5)
~~~

All Boolean independence moments of the orbit projections survive the corner
as well.  More generally, suppose only that
`e in Theta(G)' cap M` and that the compressed lamp
`eTheta(p)e` is a projection in `eMe`--equivalently,
`eTheta(a_(x_0))e` is an involution.  Compression of one projection by
another is a projection only when the two projections commute.  Hence
`[e,Theta(p)]=0`, and actor covariance then forces
`e in Theta(L(W))' cap M`.

For the Kun--Thom specialization over `F_2`, take
`Lambda=t Gamma t^(-1)` and `X=G/Lambda`.
The equivariant map `G/Lambda->G/Gamma` and
`kt-finitary-action-is-outer-mod-scalar-core` show that every nonidentity
actor moves infinitely many points of `X`.  Hence the theorem applies.
Consequently, if this explicit `W` is hyperlinear, every trace-preserving
matrix-ultraproduct embedding of `L(W)`, and every nonzero full multiplicity
corner of it, realizes the forbidden balanced projection transfer `(BWC5)`.
No amplification or commutant corner can hide the wall.

This is a sharp dichotomy, not a proof that `W` is nonhyperlinear.  The open
step remains excluding the original trace-preserving embedding; factorial
corner reduction creates no weaker model to attack.

DERIVATION
coset-wreath-full-corner-persistence-proof
