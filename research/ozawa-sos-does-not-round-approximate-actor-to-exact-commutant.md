---
rg: 2
id: ozawa-sos-does-not-round-approximate-actor-to-exact-commutant
kind: claim
title: A Kazhdan SOS certificate cannot round an approximate actor to the exact commutant of its matrices
distinct_from:
  kazhdan-stabilizer-collapses-shared-pauli-sign: that proves dimension-free shared-sign collapse when the actor coordinates are genuine representations; this proves that replacing their commutant by the exact commutant of arbitrary approximate actor matrices is impossible.
  high-type-mass-is-discontinuous-at-exact-code-tuples: that makes the generated algebra jump under a small perturbation of an exact code tuple; this quantifies the failure for commutant rounding, preserves any finite actor moment profile after amplification, and evaluates the lifted Kazhdan SOS certificate.
  property-t-does-not-kill-boolean-fiber-holonomy: that gives an exact multiplicity-cocycle obstruction after spatialization; this obstruction occurs before spatialization, at the proposed approximate-actor exactification step.
  generic-perturbations-destroy-exact-commutant-gap: that specializes the disappearing-kernel mechanism to trace-faithful regular finite-quotient coordinates of the Kun--Thom elementary actor; this gives the certificate inequality and the universal arbitrary-profile amplification.
---

**EXACT-COMMUTANT ROUNDING REFUTED; SHARED-PAULI ROUTE REMAINS OPEN.**

Let `Gamma=<S|R>` be any finite presentation with at least two named
generators, and put

~~~text
L_R=max{|r|:r in R}.
~~~

For every `eta>0` there are unitaries `U_s in U(2)` and a self-adjoint
unitary `T` such that

~~~text
max_(r in R) norm_2(U_r-I) <= L_R eta,
max_(s in S) norm_2(U_s T-T U_s) <= 2 eta,              (OSC1)
~~~

but

~~~text
{U_s:s in S}' = C I,
dist_2(T,{U_s:s in S}')=1.                              (OSC2)
~~~

Moreover the distance from `T` to every unitary in the exact commutant is
`sqrt(2)`.  Thus no modulus tending to zero can round a bounded vector which
almost commutes with an HS almost-representation to the exact commutant of
the supplied matrices.  Property (T) does not change this conclusion.

The obstruction preserves arbitrary finite actor data.  Given any tuple
`V=(V_s) in U(d)^S` and any `eta>0`, there is an irreducible tuple
`U=(U_s) in U(2d)^S` with

~~~text
max_s norm_op(U_s-V_s tensor I_2)<eta.                   (OSC3)
~~~

For `T=I_d tensor diag(1,-1)`, the commutators in (OSC1) are at most
`2 eta`, the exact commutant is scalar, and every word `w` satisfies

~~~text
norm_2(U_w-(V_w tensor I_2)) <= |w| eta,
|tr_(2d)(U_w)-tr_d(V_w)| <= |w| eta.                     (OSC4)
~~~

Hence any prescribed finite trace and relator profile is retained to
`O(eta)`.

A lifted Ozawa sum-of-squares identity does give one valid bounded-vector
estimate.  If

~~~text
Delta^2-kappa Delta=sum_i xi_i^* xi_i
~~~

holds in `C Gamma`, and the actor relators have HS defect at most
`epsilon`, then for every contraction `T`,

~~~text
kappa <Delta_U T,T>
 <= norm_2(Delta_U T)^2+C_R epsilon norm_op(T)^2.         (OSC5)
~~~

Here `C_R` depends only on one fixed lift of the certificate.  But (OSC1)-
(OSC2) show that (OSC5) cannot be upgraded to a Poincare inequality for
distance to `ker Delta_U`, which is the exact commutant.  Tiny generic
perturbations create arbitrarily small positive spectrum while deleting the
kernel.

Consequently the exact-actor compactness theorem cannot be extended by
first projecting Pauli generators into the exact commutant of a raw
approximate actor tuple.  A successful route must use a stable
near-commutant, a rounded nearby actor representation, or direct finite-word
propagation; the global nonhyperlinearity target is still **OPEN**.

DERIVATION
generic-perturbations-defeat-kazhdan-sos-rounding-proof
