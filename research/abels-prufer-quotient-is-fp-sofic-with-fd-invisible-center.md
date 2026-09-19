---
rg: 2
id: abels-prufer-quotient-is-fp-sofic-with-fd-invisible-center
kind: claim
title: An Abels Pruefer quotient is finitely presented and sofic while its central prime mark is invisible in every finite-dimensional representation
distinct_from:
  exact-fd-invisibility-has-no-general-hs-robustification: that uses the Slofstra--Vidick finitely presented sofic involution; this gives a classical solvable construction for every prime and identifies divisibility of the central subgroup as the whole exact-invisibility mechanism.
  thom-kazhdan-central-fibre-hyperlinear-nonamenable: that gives a finitely generated LEF property-(T) group but deliberately cannot be finitely presented; this gives finite presentation and amenability but not property (T).
  shared-center-pauli-tape-has-same-fp-gate: that obtains finite presentation and exact spin divisibility from an infinite Pauli tape; this shows that those two algebraic conclusions alone cannot imply normalized-HS collapse.
---

**ESTABLISHED CALIBRATION; IT DOES NOT PROVE A NONHYPERLINEAR GROUP.**

For every prime `p` there is a finitely presented amenable group `Gamma_p`
and a nonidentity central element `c_p` of order `p` such that every exact
finite-dimensional unitary representation kills `c_p`:

~~~text
rho:Gamma_p -> U(d)        implies        rho(c_p)=I.     (APQ1)
~~~

Nevertheless `Gamma_p` is sofic, and it has permutation microstates
`sigma_n` with

~~~text
||sigma_n(c_p)-I||_2 -> sqrt(2).                          (APQ2)
~~~

Here permutations are linearized as permutation matrices and the
Hilbert--Schmidt norm is normalized.

One explicit choice is obtained from the four-by-four Abels group over
`R=Z[1/p]`.  Let `A_p` be the group of upper triangular matrices

~~~text
[ 1       *       *       * ]
[ 0     p^m       *       * ]
[ 0       0     p^n       * ]
[ 0       0       0       1 ]                            (APQ3)
~~~

with off-diagonal entries in `R` and `m,n in Z`.  Write

~~~text
z(r)=I+r E_(1,4),             r in R.                    (APQ4)
~~~

The subgroup `z(R)` is central.  Put

~~~text
Gamma_p=A_p/<z(1)>,          c_p=z(1/p)<z(1)>.           (APQ5)
~~~

Abels' finite-presentation theorem gives that `A_p` is finitely presented;
quotienting by the one central relator `z(1)=1` preserves finite
presentability.  Moreover

~~~text
<z(R)>/<z(1)> isomorphic_to Z[1/p]/Z isomorphic_to C_(p^infinity), (APQ6)
~~~

so `c_p` is nontrivial and has order `p`.

The result remains false after adding a nonamenable Kazhdan factor.  Namely

~~~text
Lambda_p=Gamma_p times SL_3(Z)                            (APQ7)
~~~

is finitely presented, nonamenable and sofic, contains the commuting
property-(T) factor `SL_3(Z)`, and its same central element `c_p` still
satisfies (APQ1) and (APQ2).  This does not say that `Lambda_p` itself has
property (T); it does not.

Thus none of the following data, even taken together, is an asymptotic
central-collapse theorem:

~~~text
finite presentation;
nontrivial finite central mark;
invisibility in every exact finite-dimensional representation;
soficity or hyperlinearity of the ambient group;
nonamenability and the presence of a commuting property-(T) factor.       (APQ8)
~~~

The shared-center Kun--Thom route must use a genuinely relative analytic
input: actor/site coherence, a dimension-independent crossed-product
stability theorem, or a nonsofic-action conclusion.  Exact spin
divisibility and finite presentation alone cannot supply that input.

DERIVATION
abels-prufer-center-invisibility-and-sofic-escape-proof
