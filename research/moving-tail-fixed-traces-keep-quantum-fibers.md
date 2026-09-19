---
rg: 2
id: moving-tail-fixed-traces-keep-quantum-fibers
kind: claim
title: Canonical fixed-window traces coexist with uniformly quantum logarithmic Boolean fibers
distinct_from:
  property-t-does-not-kill-boolean-fiber-holonomy: that gives a fixed finite holonomy obstruction without canonical actor trace and a positive fixed-type character theorem; this gives canonical pointwise actor and mixed traces along a growing irreducible holonomy family.
  moving-lamp-refinement-cocycle-has-diffuse-fibers: that leaves an arbitrary Fourier multiplicity in a fixed finite action model; this uses a fixed infinite Kazhdan actor and obtains a Kazhdan-constant lower bound in every moving Boolean atom.
  coset-wreath-wall-survives-full-commutant-corners: that preserves the canonical trace in every commutant corner of the ICC Kun--Thom factor; this constructs a positive-density moving selector whose normalized corner trace is canonical, but for a trivial lamp action rather than the Kun--Thom coset action.
---

**ESTABLISHED SAME-DIMENSION NO-GO; FLEXIBLE-PADDING AND KUN--THOM
ROUTES REMAIN OPEN.**

Let `Gamma=SL_3(Z)`, fix a finite symmetric Kazhdan generating set `S`,
and use the convention

~~~text
max_(s in S)||s xi-xi|| >= kappa ||xi||                 (MTQ1)
~~~

on the orthogonal complement of invariant vectors.  For every sufficiently
large prime `p`, let `pi_p` be the nontrivial constituent of the
permutation representation of `PSL_3(F_p)` on the projective plane,
inflated to `Gamma).  Its dimension is

~~~text
r_p=p^2+p.                                               (MTQ2)
~~~

It is irreducible and nonmonomial.  For every exact monomial representation
`mu:Gamma->U(r_p)` and every unitary `Z`,

~~~text
max_(s in S)||Z pi_p(s) Z^*-mu(s)||_(2,r_p) >= kappa.   (MTQ3)
~~~

Moreover, for every fixed `g!=1` in `Gamma),

~~~text
|tr_(r_p)(pi_p(g))| <=1/p                               (MTQ4)
~~~

for all sufficiently large `p`.

Put `m_p=p` and on

~~~text
V_p=ell^2({-1,+1}^(m_p)) tensor C^(r_p)                 (MTQ5)
~~~

use the regular Boolean signs in the first tensor factor and
`U_(g,p)=I tensor pi_p(g)`.  This is an exact representation of the
direct product

~~~text
(direct_sum_N C_2) times Gamma                           (MTQ6)
~~~

after sending lamps beyond `m_p` to the identity.  Every Boolean atom in
the tested `m_p)-window has rank exactly `r_p), all covariance and actor
products are exact, and the normalized traces converge pointwise to the
canonical group trace, including every fixed mixed lamp--actor word.

The logarithmic scale is explicit.  If `D_p=dim(V_p)`, then

~~~text
D_p=2^(m_p) r_p,
m_p=log_2(D_p)-log_2(r_p)
   =log_2(D_p)-O(log log D_p).                           (MTQ7)
~~~

Nevertheless each moving atom has the corner-normalized obstruction
`(MTQ3)`.  More generally let `e_p` be the sum of the atoms whose last
Boolean sign is `+1`.  Then

~~~text
tr(e_p)=1/2,
||x||_(2,e_p)^2=2 tr_(D_p)(e_p x^*x e_p),               (MTQ8)
~~~

and the compressed sequence still has the canonical trace on every fixed
group word.  For arbitrary atomwise gauges and atom-preserving exact
monomial targets,

~~~text
max_(s in S)||e_p(ZU_(s,p)Z^*-M_(s,p))e_p||_(2,e_p)
 >= kappa/sqrt(|S|).                                    (MTQ9)
~~~

Thus fixed-window Boolean spatialization, canonical pointwise mixed traces,
a positive-density normalized corner, and actor property `(T)` do not give
same-dimension control at a logarithmically moving window.

The example also identifies its exact limitation.  The projective
permutation representation is

~~~text
1 direct_sum pi_p.                                      (MTQ10)
~~~

Adding one trivial dimension to every moving atom makes the cocycle exactly
permutation.  The total padding ratio is

~~~text
2^(m_p)/(2^(m_p) r_p)=1/r_p ->0.                        (MTQ11)
~~~

Hence the countermodel does not refute flexible normalizer transfer after
`o(D_p)` padding.  It proves that such padding is load-bearing, not a
technical convenience.  The lamp action here is trivial; no conclusion
about hyperlinearity of the pinned Kun--Thom coset wreath is claimed.

DERIVATION
moving-tail-projective-space-countermodel-proof
