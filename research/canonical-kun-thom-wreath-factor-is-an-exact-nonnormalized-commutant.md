---
rg: 2
id: canonical-kun-thom-wreath-factor-is-an-exact-nonnormalized-commutant
kind: claim
title: The canonical Kun--Thom wreath factor has an exact nonnormalized relative commutant
distinct_from:
  kt-centralizer-normalization-hs: that asks whether the matrix-ultraproduct hypothesis restores normalization; this proves normalization is false in the canonical finite tracial wreath algebra and makes Connes embeddability the exact remaining fork.
  kt-pair-non-hyperlinear-commutant: that records the conditional lamp contradiction from a positive normalization theorem; this packages the converse as an explicit counterrepresentation whenever the pinned wreath product is hyperlinear.
  nonsofic-wreath-product: that proves the same group is nonsofic through permutation cluster rigidity; this computes its von Neumann relative commutant without assuming a permutation model.
---

Let `Gamma<G` be infranormal and nonnormal.  Put

~~~text
X=G/Gamma,
W=(direct_sum_X C_2) semidirect G,
N=L(W),                                                   (KWF1)
~~~

and let `sigma(g)=lambda_W(g)`.  If `a_x` denotes the nontrivial lamp at
`x in X`, then

~~~text
a_Gamma in sigma(Gamma)' intersect N,                    (KWF2)
~~~

but this relative commutant is not normalized by `sigma(G)`.

Indeed, infranormality and nonnormality give a strict compressor
`t in G` with

~~~text
t Gamma t^(-1) proper_subset Gamma.                      (KWF3)
~~~

Choose `gamma in Gamma minus t Gamma t^(-1)`.  Then

~~~text
sigma(t) a_Gamma sigma(t)^*=a_(tGamma),
sigma(gamma) a_(tGamma) sigma(gamma)^*=a_(gamma tGamma)
                                      !=a_(tGamma).       (KWF4)
~~~

The failure is quantitative in the canonical trace:

~~~text
||a_(gamma tGamma)-a_(tGamma)||_2=sqrt(2).               (KWF5)
~~~

The same calculation with `q_x=(1+a_x)/2` gives two projections at
distance `1/sqrt(2)`.

Consequently the unitary-ultraproduct analogue of Kun--Thom Theorem 4.1
has an exact dichotomy for this pinned source.

- If `W` is hyperlinear, a trace-preserving embedding
  `Theta:L(W)->product_U M_(d_n)` makes
  `Theta circle sigma:G->U(product_U M_(d_n))` a
  trace-faithful hyperlinear representation whose `Gamma`-commutant is
  not `G`-normalized.
- If every trace-faithful matrix-ultraproduct representation of `G` has
  normalized `Gamma`-commutant, then `W` is nonhyperlinear.

Thus property `(T)` and infranormality do **not** force normalization in
an arbitrary finite tracial representation.  The matrix-ultraproduct
hypothesis is the entire live content.  Proving it for the pinned pair
solves the nonhyperlinear-group problem; refuting it produces a
hyperlinear nonsofic wreath product.

The Aug-2026 permutation proof identifies the exact missing structure.
Kun--Thom first represent every permutation centralizer element by a total
bisection of a finite cluster groupoid.  A compressor gives a faithful
functor between conull restrictions.  Median control makes orbit and
isotropy cardinality ratios tend to one; since the residual isotropy index
is an integer below two, the functor is onto, and the transported
bisection can be completed.

For `sigma(Gamma)' intersect product_U M_(d_n)` there is no known total
bisection description, finite isotropy order, or integer-index
surjectivity step.  Property `(T)` supplies spectral gap for the exact
adjoint representation on `L^2`, but (KWF2)--(KWF5) show that spectral gap
alone cannot turn a vector fixed by `t Gamma t^(-1)` into one fixed by
`Gamma`.  Alekseev--Thom Open Problem 6.2 asks for precisely the missing
coordinate description of such a matrix commutant.

The global route remains **OPEN**: establish the coordinate/cluster
replacement in the matrix ultraproduct and obtain a nonhyperlinear `W`,
or embed the exact countermodel (KWF1) and thereby refute normalization.

DERIVATION
strict-compressor-lamp-commutator-and-ce-dichotomy-proof
