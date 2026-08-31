---
rg: 2
id: gamma-only-exactification-preserves-the-diagonal-but-not-the-kt-return
kind: claim
title: Gamma-only exactification preserves the diagonal mass but does not control the Kun--Thom return
artifacts:
  - research/kt-diagonal-commutant-expectation-and-finite-wreath-countermodel-proof.md
distinct_from:
  kt-elementary-kazhdan-packet-rounds-base-lamp: That rounds a projection into the commutant of a supplied genuine Gamma representation; this additionally tracks the conditional expectation back to the BCJM diagonal and proves that Gamma-only data still permit the full named-return displacement.
  kt-full-kazhdan-majorana-return-collapses-in-fd: That assumes a genuine representation of the Laurent elementary actor containing h; this proves by exact finite models that a genuine representation of Gamma alone cannot replace that hypothesis.
  amenable-lamp-rounding-preserves-the-kt-named-return-wall: That produces the diagonal half-set from a hypothetical wreath microstate; this audits what actor exactification would and would not do to it.
---

**ESTABLISHED CONDITIONAL ROUNDING AND EXACT FIREWALL; THE ROOT REMAINS OPEN.**

In the pinned `q=2,r=3` pair,

~~~text
Gamma=EL_3(F_2[x_1,x_2,x_3]).
~~~

Let `K` be the explicit elementary Kazhdan packet and let
`kappa_K>0` be its Kazhdan constant. Let `D subset M_d` be any diagonal
masa, let `p in D` be a projection, and let `u_s`, `s in K`, be
unitaries. Suppose that a genuine representation

~~~text
pi:Gamma -> U(d)
~~~

satisfies

~~~text
epsilon=max_(s in K)||u_s-pi(s)||_2,
delta=max_(s in K)||[p,u_s]||_2.
~~~

Then there is a projection `P in pi(Gamma)'` such that, with
`E_D:M_d->D` the trace-preserving conditional expectation and
`a=E_D(P)`,

~~~text
||p-P||_2 <= eta,
||p-a||_2 <= eta,
||P-a||_2 <= eta,                                      (GDE1)

eta=(sqrt(2)/kappa_K)(delta+2 epsilon).                  (GDE2)
~~~

Thus exactifying the Gamma restriction does not wash out the BCJM diagonal
half-set. Its commutant projection has a diagonal conditional expectation
with the same dimension-free error. Thresholding `a` at `1/2` gives a
diagonal projection `e` with

~~~text
||e-p||_2 <= 2 eta.                                     (GDE3)
~~~

This positive fact does **not** control the return. There is an exact
trace-faithful finite-dimensional sequence with all of the following
properties simultaneously:

1. the Gamma matrices are genuine and have the canonical trace;
2. `p` is a literal diagonal half-rank projection in their commutant;
3. the external return unitary normalizes the Gamma image exactly; and
4. the return wall is exact:

~~~text
||[p,U]||_2=1/sqrt(2).                                  (GDE4)
~~~

The model is the tensor product of regular finite quotients of `Gamma`
with the regular representation of

~~~text
F=(C_2)^4 rtimes C_4,
~~~

where `C_4` cyclically permutes the four lamp sites. Fourier transform on
the finite Boolean lamp makes `p=(1+lambda_F(z_0))/2` diagonal, and the
generator `t in C_4` sends it to
`(1+lambda_F(z_1))/2`. The regular character gives squared distance
exactly `1/2`.

This is not a countermodel to the full Kun--Thom actor. In a genuine
finite-dimensional representation of the Laurent elementary group

~~~text
E=EL_3(F_2[x_1^(+-1),x_2^(+-1),x_3^(+-1)]),
~~~

finite-image compression puts the named
`h=e_12(x_2/x_1)` in the image of `Gamma`, so a
`pi(Gamma)`-central projection is automatically `pi(h)`-central. The
countermodel proves that this conclusion uses extension to `E`, not
property `(T)`, diagonal structure, canonical trace, or exactification of
`Gamma` alone.

## Literature fence

No published theorem found in the audited stability literature supplies the
needed exactification for this concrete source.

- Becker--Lubotzky, arXiv:1809.00632, rules out unrestricted
  same-dimensional normalized-HS stability for every infinite hyperlinear
  property-`(T)` group, hence for this residually finite `Gamma`.
- The Lavi--Levit character theorem, arXiv:2007.15547, assumes elementary
  rank strictly above the stable range of the coefficient ring. Its stated
  general hypothesis does not yield the pinned rank-three case: the standard
  dimension bound gives only `stable_range(R)<=4`, not the required
  `3>stable_range(R)`.
- Character rigidity or hyperfinite-HS stability would in any event control
  only the appropriate limiting-character sector; the canonical wreath
  restriction has regular character and nonamenable GNS algebra.
- Flexible HS or weak-ucp stability for this universal-lattice group is not
  established by those sources. Even the analogous claim for
  `SL_3(Z)` remains a separate open stability problem.

Accordingly, a successful actor bridge must exactify the source-specific
`K union {h}` interface into one representation of `E` (possibly after
controlled padding). Gamma-only exactification plus diagonal conditioning is
provably insufficient.
