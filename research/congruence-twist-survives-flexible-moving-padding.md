---
rg: 2
id: congruence-twist-survives-flexible-moving-padding
kind: claim
title: A congruence twist keeps logarithmic Boolean fibers quantum after sublinear padding
distinct_from:
  moving-tail-fixed-traces-keep-quantum-fibers: that uses the zero-sum projective representation and is absorbed by one padding line per atom; this tensors with a fixed Klein representation and proves a monomial-carrier gap larger than the whole original fiber.
  property-t-does-not-kill-boolean-fiber-holonomy: that gives padding-stable nonmonomial holonomy for a fixed finite property-T group but lacks canonical actor trace; this gives canonical pointwise traces for the fixed infinite actor SL_3(Z).
  shared-center-extraspecial-wreath-has-fd-invisible-spin-sector: that leaves a Fourier multiplicity after a fixed Pauli window; this produces a padding-stable multiplicity representation with an explicit Kazhdan lower bound.
---

**ESTABLISHED FLEXIBLE ATOMWISE NO-GO FOR A TRIVIAL LAMP ACTION;
THE KUN--THOM COSSET ACTION REMAINS OPEN.**

Let `Gamma=SL_3(Z)`, fix a finite symmetric Kazhdan generating set `S`,
and let `kappa>0` be its Kazhdan constant in the convention (MTQ1).
There is an infinite sequence of primes `p congruent 3 mod 7` and
irreducible representations

~~~text
sigma_p:Gamma->U(d_p),             d_p=3p(p+1),          (CTP1)
~~~

with the following three properties.

First, their normalized characters converge to the canonical character with
the explicit pointwise rate

~~~text
|tr_(d_p)(sigma_p(g))|<=1/p                             (CTP2)
~~~

for every fixed `g!=1` and all sufficiently large `p).

Second, every monomial representation of `Gamma` which contains
`sigma_p` has dimension at least

~~~text
7(p^2+p+1)>2d_p.                                        (CTP3)
~~~

Third, if `alpha` is any exact representation of dimension `q<=d_p`,
`mu` is any exact monomial representation of dimension `d_p+q`, and
`Z` is unitary, then

~~~text
max_(s in S)
 ||Z(sigma_p direct_sum alpha)(s)Z^*-mu(s)||_(2,d_p+q)
 >=kappa sqrt(d_p/(d_p+q)).                              (CTP4)
~~~

The construction is explicit.  Let `xi_p` be the zero-sum constituent of
the projective-plane permutation representation of `PSL_3(F_p)`, let
`H=PSL_3(F_2)` and let `rho` be either three-dimensional Klein
irreducible of `H`.  Chinese remaindering gives a quotient

~~~text
Gamma -> PSL_3(F_p) times H,
sigma_p=xi_p tensor rho.                                 (CTP5)
~~~

For `m_p=p`, place `sigma_p` in every atom of the regular
`m_p`-lamp Boolean algebra and let `Gamma` act trivially on the lamp
labels.  The exact models have

~~~text
D_p=2^(m_p)d_p,
m_p=log_2(D_p)-O(log log D_p).                           (CTP6)
~~~

All Boolean moments, actor products, covariance equations, and fixed mixed
traces are canonical in the limit.

Let `e_p` select the atoms whose last, moving lamp sign is `+1`.
Then `tr(e_p)=1/2`, the normalized corner sequence is still canonical on
every fixed group word, and the following remains true after arbitrary
atomwise padding of total dimension `Q_p=o(D_p)`: for every atomwise gauge
and every exact atom-preserving monomial actor target,

~~~text
max_(s in S)||e_p(ZU_(s,p)Z^*-M_(s,p))e_p||_(2,e_p)
 >=kappa/sqrt(|S|)-o(1).                                (CTP7)
~~~

Thus property `(T)`, exact fixed-window Boolean spatialization, canonical
pointwise mixed traces, full positive-density corner normalization, and even
sublinear flexible padding do not control the unitary cocycle in a
logarithmically moving atom.  The construction uses the trivial action of
`Gamma` on the lamps.  It therefore rules out arguments based only on the
listed analytic inputs, but it does not rule out a theorem using the
specific nontrivial Kun--Thom coset action.

DERIVATION
congruence-twist-padding-stable-countermodel-proof

## Attempts

(Repair note: invalid requires-block removed from a claim; the authoring lane's route carries the attack.)
