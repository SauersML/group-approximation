---
rg: 2
id: finite-pattern-projective-decoder-proof
kind: route
title: Identify finite pattern orbits as projectives over Q[G] and apply characteristic-zero finiteness
target: finite-pattern-orbit-closure-forces-surjunctivity
requires:
  - stable-finiteness-reduces-to-prime-field
---

## Rational local observables have a translation-permuted basis

Let O be the rational vector space of functions A^G->Q depending on
finitely many coordinates. On each finite set of sites F, the products
of the site basis {1,psi_1,...,psi_(|A|-1)} form a tensor-product basis of
all functions A^F->Q. Inclusions of site sets preserve these bases by
tensoring with 1. Thus O has a basis consisting of 1 and all nonempty
colored pattern monomials described in the claim.

Use the left G-action on observables (g.f)(x)=f(g^(-1).x), where the
configuration action is the left shift. This translates supports and
preserves their basis colors, so G permutes the nonconstant basis.
Equivariance of tau and sigma makes their pullbacks Q[G]-linear.

## Each nonconstant pattern orbit is a finitely generated projective

Let m have nonempty finite support F, and let H be its stabilizer in G.
If h fixes m, then hF=F, by uniqueness of the tensor basis. Fix f in F.
The map H->F given by h->hf is injective, so H is finite.

The span of the orbit of m is the permutation module Q[G/H]. With

    e_H=|H|^(-1) sum_(h in H) [h] in Q[G],

this module is isomorphic to the left ideal Q[G] e_H. Indeed the distinct
coset averages [g]e_H are linearly independent and indexed by G/H.
Since e_H is idempotent, the module is finitely generated projective.

Distinct basis orbits have independent spans. Consequently

    P=W/(Q 1)

is a finite direct sum of such projectives. This quotient removes the
constant observable without assuming that the pullbacks preserve a
chosen nonconstant complement.

## A projective observable module cannot support a strict inverse pair

By the characteristic-zero part of
stable-finiteness-reduces-to-prime-field, Q[G] is stably finite for every
group G. The endomorphism ring of a finitely generated projective left
Q[G]-module is a corner of a matrix ring over Q[G]^op and is directly
finite. Stable finiteness passes to the opposite ring. Corner finiteness
follows by adding the complementary idempotent to the two factors of a
one-sided inverse pair and applying matrix finiteness.

Write T=tau^* and S=sigma^*. From sigma tau=id we have T S=id on O.
The assumed invariance of W, and the fact that every pullback fixes 1,
give induced endomorphisms Tbar,Sbar of P with Tbar Sbar=id. Direct
finiteness of End_(Q[G])(P) gives Sbar Tbar=id too.

It follows that for every one-site observable f in W,

    (S T-I)f = f composed with tau sigma - f

is a constant function. This constant is zero: on any point x=tau(y)
of the nonempty image of tau, the identity sigma tau=id makes
tau sigma(x)=x. Hence tau sigma preserves every one-site psi_i observable.
The site basis separates symbols, so tau sigma=id on all configurations.
The one-symbol alphabet is trivial and needs no projective argument.

## Every injective full-shift automaton has a local decoder

For completeness, an injective tau is a homeomorphism from the compact
space A^G onto its closed image. The coordinate at 1 of its inverse is
continuous and finite-valued, so it depends on a finite set of output
coordinates. One can see finite dependence by taking a finite cylinder
cover of the image on which that coordinate is constant. Define a local
rule on the patterns occurring in the image by this inverse coordinate,
and assign arbitrary alphabet values on all other patterns. Translating
this rule gives a cellular automaton sigma on the whole full shift with
sigma tau=id. This extension does not assert tau sigma=id.

## What finite closure means, and why growth alone is insufficient

Start with representatives of the one-site basis orbits. Expand tau^*m
and sigma^*m in the tensor basis for each current representative m; add
the translation orbits of all nonconstant monomials with nonzero
coefficients. Repeat. Each stage is finite, since both rules have finite
memory. If the union contains finitely many orbits, it stabilizes and
defines a W satisfying the theorem. Therefore a hypothetical strict
embedding forces infinitely many orbits for every decoder. This is an
algebraic closure process; no decidable word-problem assumption or
algorithmic stopping bound is asserted.

For the displayed Z-example, substitution verifies both sigma tau=id
and tau sigma=id. Its n-th iterate has first track

    first_track(tau^n(a,b))_j = a_j XOR b_j XOR ... XOR b_(j+n-1).

As a rational-valued function, XOR of binary variables z_0,...,z_n is

    (1-product_(i=0)^n(1-2 z_i))/2.

Use the site basis {1,a,b,ab} for the alphabet {0,1}^2. The expansion at
j=0 contains the nonzero monomial

    (ab)_0 b_1 ... b_(n-1),     coefficient (-2)^n.

Its support has n sites, so these monomials belong to different
translation orbits as n grows. Any pullback-invariant span of pattern
basis orbits containing the first-track coordinate must contain all of
them. Thus the finite-closure criterion fails even for this explicit
reversible automaton. Infinite growth is a necessary feature of a
counterexample under this test, not a counterexample certificate.
