---
rg: 2
id: boolean-secants-do-not-supply-operator-left-inverses
kind: claim
title: Boolean inverse identities do not yield operator inverse identities by ordinary differentiation or telescoping secants
distinct_from:
  certificate-linear-counterexamples-compile-to-lamp-algebras: that compiles a genuinely injective certificate-controlled linear family; this disproves the proposed way of obtaining such a family from an arbitrary nonlinear encoder by coordinatewise finite differences.
  finite-pattern-orbit-closure-forces-surjunctivity: that constrains finite closure of rational pattern observables; this identifies the failure of two first-order linearizations over F_2.
---

Two facts constrain an attempted nonlinear-to-linear compiler for
finite-alphabet cellular automata.

1. The Boolean function algebra

       R=F_2[x_i:i in I]/(x_i^2-x_i:i in I)

   has zero module of Kahler differentials over F_2, for any index set I.
   Differentiating a chosen polynomial representative is not an intrinsic
   derivative of the represented Boolean function. In particular, a
   full-shift inverse identity valid as a Boolean function need not give
   a matrix inverse identity after formal differentiation of representatives.

2. The canonical coordinate-telescoping secant matrix of a Boolean
   permutation can be singular. An explicit involution of F_2^3 is

       t=b(1+a+c),
       F(a,b,c)=(a+t,b,c+t).

   For x=000 and y=111, with coordinate order a,b,c, its secant matrix is

       D_F(x,y) = [1 0 1]
                  [0 1 0]
                  [0 0 0].

   It correctly sends y-x=111 to F(y)-F(x)=010, but kills the nonzero
   vector 101. Thus the operator family defined by these matrices is
   not injective, although the original Boolean map is reversible.

For an encoder tau with decoder sigma, this construction gives the
identity

    D_sigma(tau(x),tau(y)) D_tau(x,y) (y-x)=y-x,

but not, in general, D_sigma D_tau=I as an operator identity on arbitrary
vectors. Treating (x,y) as a certificate does not remove that distinction.
The certificate-controlled linear compiler needs injectivity for every
data vector with a fixed certificate, not only its encoded disagreement.

This refutes these particular differentiation and telescoping constructions.
It does not exclude other nonlinear encodings or other choices of secant
operators. The involution is a local gate and therefore gives the same
counterexample as a sitewise reversible cellular automaton over any group.

Three bits is minimal for this phenomenon among Boolean permutations:
every permutation on one or two bits is affine and has constant invertible
telescoping secants. Moreover, in any finite dimension, invertible secants
with an exact composition law can be chosen for every permutation by
choosing a frame for each nonzero disagreement vector. This latter
construction is a finite-space fact; it supplies no uniform finite-memory
construction for arbitrary cellular automata.
