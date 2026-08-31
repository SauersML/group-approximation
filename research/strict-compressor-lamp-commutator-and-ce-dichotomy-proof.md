---
rg: 2
id: strict-compressor-lamp-commutator-and-ce-dichotomy-proof
kind: route
title: Compute the exact wreath commutant defect and locate the matrix-only gate
target: kun-thom-wreath-factor-is-exact-nonnormalized-commutant
requires:
  - kt-centralizer-normalization-hs
  - non-hyperlinear-group
---

# The canonical wreath algebra is the exact counterprofile

Let `Gamma<G` be infranormal and nonnormal and let

~~~text
P_Gamma={g in G:g Gamma g^(-1) subset Gamma}.
~~~

Since `P_Gamma` generates `G`, some `t in P_Gamma` is a strict
compressor.  Otherwise every element of `P_Gamma` would normalize
`Gamma`, hence so would the group it generates, contrary to nonnormality.
Put

~~~text
Lambda=t Gamma t^(-1) proper_subset Gamma.                (1)
~~~

Let `X=G/Gamma` and
`W=(direct_sum_X C_2) semidirect G`.  Write `a_x` for the nontrivial
lamp at `x` and use the canonical group unitaries in `N=L(W)` without
changing notation.

## 1. Exact failure of normalization

For `gamma in Gamma`,

~~~text
gamma a_Gamma gamma^(-1)=a_(gamma Gamma)=a_Gamma.         (2)
~~~

Thus `a_Gamma in sigma(Gamma)' intersect N`, where
`sigma(g)=lambda_W(g)`.  Conjugating by the strict compressor gives

~~~text
t a_Gamma t^(-1)=a_(tGamma).                              (3)
~~~

Choose `gamma_0 in Gamma minus Lambda`.  Equality of the two cosets
`gamma_0 tGamma=tGamma` would imply
`t^(-1)gamma_0 t in Gamma`, equivalently
`gamma_0 in Lambda`.  Hence the cosets are distinct and

~~~text
gamma_0 a_(tGamma) gamma_0^(-1)
 =a_(gamma_0 tGamma)
 !=a_(tGamma).                                            (4)
~~~

Equations (2)--(4) prove that the relative commutant is not normalized.

The defect has fixed normalized `L^2` size.  Distinct lamps are commuting
self-adjoint involutions and their product is a nonidentity group element.
The canonical trace therefore gives

~~~text
||a_x-a_y||_2^2
 =tau((a_x-a_y)^*(a_x-a_y))
 =2-2 tau(a_x a_y)
 =2                                                        (5)
~~~

whenever `x!=y`.  In particular, the commutator defect in (4) is
`sqrt(2)`.  If `A=sigma(Gamma)' intersect N`, then for every `z in A`,

~~~text
sqrt(2)
 =||[a_(tGamma),sigma(gamma_0)]||_2
 <=2||a_(tGamma)-z||_2.                                  (6)
~~~

Thus `dist_2(a_(tGamma),A)>=1/sqrt(2)`.  This is not a weak-closure or
choice-of-representative artifact.

The projection version is obtained from `q_x=(1+a_x)/2`.  One has
`q_Gamma in A` and

~~~text
||q_(gamma_0 tGamma)-q_(tGamma)||_2=1/sqrt(2).            (7)
~~~

## 2. The matrix-ultraproduct dichotomy

Assume `W` is hyperlinear.  Equivalently, its canonical trace gives a
trace-preserving embedding

~~~text
Theta:L(W) -> product_U M_(d_n).                          (8)
~~~

Then `rho=Theta circle sigma` is a trace-faithful hyperlinear
representation of `G`.  Trace preservation and multiplicativity carry
(2)--(6) into the matrix ultraproduct without changing their norms.
Therefore

~~~text
rho(Gamma)' intersect product_U M_(d_n)
~~~

is not normalized by `rho(G)`.

The contrapositive is the useful direction: if every trace-faithful
matrix-ultraproduct representation of this `G` has normalized
`Gamma`-commutant, then (8) cannot exist and `W` is nonhyperlinear.
Thus the following fork is unconditional:

~~~text
W is nonhyperlinear,
or
W is hyperlinear and its canonical CE embedding refutes
unitary-ultraproduct centralizer normalization.           (9)
~~~

Property `(T)` is used by the proposed positive theorem, not by the exact
counterprofile.  Equations (2)--(7) show why property `(T)` alone is
insufficient in arbitrary finite tracial algebras.

## 3. The automatic inclusion and the hard inclusion

For any homomorphism `rho:G->U(M)` into a finite tracial algebra, put

~~~text
A_Gamma=rho(Gamma)' intersect M,
A_Lambda=rho(Lambda)' intersect M.
~~~

From `Lambda subset Gamma` one has `A_Gamma subset A_Lambda`.  Conjugation
gives

~~~text
Ad(rho(t))(A_Gamma)=A_Lambda.                             (10)
~~~

Hence normalization by `t` is exactly the reverse containment

~~~text
(CCR)   A_Lambda subset A_Gamma.                          (11)
~~~

The wreath element `a_(tGamma)` belongs to the left side of (11) and,
by (4), not to the right side.  The matrix problem is therefore not to
derive one-sided inclusion; it is to prove that an exact proper
self-compression of the fixed space cannot occur inside a tracial matrix
ultraproduct carrying the canonical group trace.

On `L^2(M)`, `Ad(rho)` is a genuine unitary representation even when
coordinate lifts are only approximate representations.  Property `(T)`
gives spectral gap from the `Gamma`-fixed space, but it does not identify
the larger `Lambda`-fixed space with it.  The vector in (6) is already
exactly `Lambda`-fixed and uniformly far from the `Gamma`-fixed space.
Any positive argument must use matrix-coordinate structure in addition
to spectral gap.

## 4. Source-accurate audit of the permutation proof

Kun--Thom, arXiv:2608.06222v3, Theorem 4.1 proves the permutation
analogue.  The proof uses the following discrete chain.

1. Kun's expander decomposition cuts a sofic approximation of `Gamma`
   into finite expander components.
2. The Alekseev--Thom cluster theorem represents every permutation in
   the ultraproduct centralizer by patched arrows of a total bisection
   of a finite cluster groupoid.  This is Lemma 4.2(4) in the
   Kun--Thom joint-scale formulation.
3. A compressor produces a faithful functor between conull restrictions
   of two such groupoids.  The two median arguments control the orbit
   cardinality `o_n(i)` and the finite isotropy order `k_n(i)`.
4. In the proof of Theorem 4.1, the induced isotropy map is injective and
   its index tends to one.  The index is a positive integer, so it is
   eventually below two and therefore equals one.  The Hom-set map,
   being a map of finite torsors, is then bijective.
5. The transported partial bisection can consequently be completed
   inside each connected component on negligible vertex mass.  This
   yields the hard containment (11) for permutation centralizers.

The integer-index step is not an ornamental estimate.  It upgrades an
injective transported cluster functor to a full one and thereby produces
preimages for every arrow of an arbitrary centralizer bisection.

## 5. Exact missing unitary step

For a unitary matrix ultraproduct, an element of

~~~text
rho(Gamma)' intersect product_U M_(d_n)
~~~

is an arbitrary bounded matrix sequence which asymptotically commutes
with each fixed group element.  No theorem currently represents every
such element by total bisections of finite objects.  There is therefore
no coordinate orbit count, finite isotropy order, or Hom-torsor on which
the argument in Section 4 can run.

Alekseev--Thom, arXiv:2608.05362, Open Problem 6.2 asks whether, after
`o(d_n)` padding, the commutant of a Kazhdan matrix-ultraproduct
representation is an ultraproduct of finite-dimensional star-subalgebras,
and whether these can be chosen as centralizers of generator lifts.  Even
a positive answer must be used in a joint relative form here: the
coordinate descriptions for `Gamma` and `Lambda` must be compatible with
the same lifts of `rho(t)`, and the one-sided inclusion in (10) must be
upgraded uniformly on the operator-norm unit balls.  This is the matrix
replacement for cluster-functor fullness.

The canonical wreath calculation proves that such a theorem cannot hold
in all finite tracial algebras.  Its only possible source is the internal
finite-dimensional geometry of a CE embedding.  Establishing that
geometry proves the first branch of (9); constructing (8) proves the
second.  No branch is claimed here.

## References

- G. Kun and A. Thom, *Nonsofic wreath products of residually finite
  groups*, arXiv:2608.06222v3, especially Theorem 4.1, Lemmas 4.2--4.4,
  and the proof of Theorem A.
- V. Alekseev and A. Thom, *Centralizers of sofic approximations of
  Kazhdan groups*, arXiv:2608.05362, Proposition 4.5 and Open Problem
  6.2.
