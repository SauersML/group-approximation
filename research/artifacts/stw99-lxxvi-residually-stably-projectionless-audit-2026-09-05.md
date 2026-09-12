# Full Cu regularity without projection-bearing quotients

## Theorem

Every separable pure C*-algebra A whose every quotient is stably
projectionless is Cu-regular for the actual first-factor inclusion.
Consequently, for a separable simple stably projectionless pure D,
`C0(X,D)` is pure and Cu-regular for every second-countable locally
compact Hausdorff X, in arbitrary dimension.

The proof treats all positive elements. It does not merely compute V,
K-theory, or a pointwise evaluation invariant.

## 1. The softness conventions

There are two conventions to keep separate. A positive operator a is
soft in the operator sense when `Her(a)` has no nonzero unital quotient.
A Cu class x is functionally soft in the APT sense if, for every
`x'<<x`, there is k with `(k+1)x'<=kx`. Strong softness is a stronger
abstract condition involving a complementary element that generates
the same ideal.

We use the following published implications from Thiel--Vilalta,
*Soft operators in C*-algebras*: the spectral characterization in
Proposition 3.6, the passage from operator softness to strong softness
in Proposition 4.16 (arXiv numbering), and strong softness implying
functional softness in Proposition 4.5. In the residually stably finite
setting their Corollary 4.6 and Proposition 4.16 identify these conventions.

Our Cu-isomorphism input,
`stw99-lxxvi-first-factor-soft-cu-isomorphism`, uses functional softness.
Thus establishing strong softness below is more than sufficient.

## 2. No projection in a quotient means every positive class is soft

Let B be residually stably projectionless, and take
`a in (B tensor K)_+`. Every closed ideal of `B tensor K` is `I tensor K`
for some ideal I of B, and its quotient is `(B/I) tensor K`.

For each such quotient let b be the image of a. If b is nonzero and its
spectrum does not accumulate at zero, continuous functional calculus
gives its nonzero support projection

```text
chi_(0,infinity)(b) in (B/I) tensor K.
```

This contradicts stable projectionlessness of B/I. Hence every
quotient image of a is either zero or has spectrum accumulating at
zero. The spectral criterion makes a a soft operator, so [a] is
functionally soft. Since a was arbitrary,

```text
Cu(B) = Cu(B)_soft.
```

For an independent check of the finiteness convention, a stably
projectionless B is stably finite in the unitization sense. An isometry
in `M_n(tilde B)` has a unitary scalar image, so its defect projection
lies in `M_n(B)` and is zero. Apply this to every quotient of B. Thus
the residually stably finite equivalence of the softness notions is
also applicable.

## 3. Z cannot create a projection over a stably projectionless algebra

Let B be any stably projectionless C*-algebra. Write Z as its standard
inductive limit of prime dimension-drop algebras `Z_(n_j,n_j+1)`.
Then

```text
(B tensor Z) tensor K
  = lim_j B tensor Z_(n_j,n_j+1) tensor K.
```

Suppose the limit contains a nonzero projection q. Projection stability
in C*-inductive limits gives a projection p in one stage whose image is
Murray--von Neumann equivalent to q. This is the usual finite-stage
projection perturbation argument, and does not assume real rank zero
of B. In particular p is nonzero.

The stage embeds into

```text
C([0,1], B tensor M_(n_j(n_j+1)) tensor K).
```

That embedding remains injective after tensoring by B because the
minimal tensor product is injective on inclusions; exactness of B is
not needed. A nonzero projection section p has a nonzero evaluation at
some point, which is a nonzero projection in `B tensor K` after matrix
identification. This is a contradiction. Thus B tensor Z is stably
projectionless.

## 4. Every target quotient is covered

The load-bearing tensor-ideal theorem is Gupta--Jain,
*On closed Lie ideals of certain tensor products of C*-algebras*,
Theorem 3.1: if one factor is simple and exact, every closed ideal
of its minimal tensor product with an arbitrary C*-algebra is a
product ideal. Apply it with the simple exact factor Z. Therefore
every ideal J of `A tensor Z` has the form `I tensor Z` for a closed
ideal I of A.

Since Z is exact, the corresponding quotient is canonically

```text
(A tensor Z)/(I tensor Z) ~= (A/I) tensor Z.
```

Each A/I is stably projectionless by hypothesis, so Section 3 shows
that every such target quotient is stably projectionless. This proves
the required residual property for `A tensor Z`; it is not inferred
from stable projectionlessness of the whole target alone.

Applying Section 2 to source and target gives

```text
Cu(A)=Cu(A)_soft,
Cu(A tensor Z)=Cu(A tensor Z)_soft.
```

## 5. Complete regularity

A is pure by assumption. The soft first-factor theorem therefore
makes its actual map an isomorphism between the two soft parts.
Section 4 identifies those parts with the whole semigroups. Hence

```text
Cu(A) --Cu(a|->a tensor 1)--> Cu(A tensor Z)
```

is a Cu-isomorphism. This includes surjectivity, equality reflection,
all order relations, and the way-below structure.

## 6. Arbitrary-dimensional simple-fiber fields

Let D be simple, separable, stably projectionless, and pure, and let
X be second-countable locally compact Hausdorff. Every ideal of
`C0(X,D)` is of the form `C0(U,D)` for an open U in X, and the quotient
is `C0(X minus U,D)`. This follows from the same tensor-ideal theorem
using its alternative hypothesis that the commutative factor is
nuclear (no exactness assumption on D). Restriction onto a closed set
is surjective, equivalently the associated tensor quotient is exact
because the commutative extension is nuclear.

Every such quotient is stably projectionless: a projection in its
stabilization evaluates at each point to a projection in `D tensor K`,
so is zero at every point. Thus the field is residually stably
projectionless.

For compact metrizable X, Seth--Vilalta Theorem A proves purity of
`C(X,D)`, with no dimension restriction. For noncompact X, use its
metrizable one-point compactification X-plus and the ideal
`C0(X,D)` of `C(X-plus,D)`. Purity passes to ideals. The theorem in
Section 5 now gives complete Cu regularity in both cases.

The only topological hypotheses needed here ensure separability and
the applicability of the stated purity theorem. In particular X may
be an arbitrary sphere, an infinite-dimensional compact metrizable
space, or a noncompact space of unbounded covering dimension.

## Primary sources and prior-art boundary

- H. Thiel and E. Vilalta, *Soft operators in C*-algebras*, especially
  Proposition 3.6 and the comparisons between operator/strong/functional
  softness in Section 4: https://arxiv.org/pdf/2304.11644 .
- V. P. Gupta and R. Jain, *On closed Lie ideals of certain tensor
  products of C*-algebras*, Theorem 3.1 and Proposition 5.1:
  https://arxiv.org/pdf/1701.02218 . Theorem 3.1 explicitly allows an
  arbitrary other factor when the simple factor is exact.
- A. Seth and E. Vilalta, *Continuous functions over a pure C*-algebra*,
  Theorem A: https://arxiv.org/pdf/2602.14809 .
- The canonical realification and W-tensor results supplying the soft
  isomorphism are APT Corollary 7.5.10 and Proposition 7.5.12:
  https://arxiv.org/pdf/1410.0483 . Their map-level application is proved
  in the separate soft-isomorphism artifact.

The published structural and tensor results above are inputs. The new
conclusion in this lane is their combination into the actual full
first-factor theorem for residually stably projectionless pure
algebras, including the all-dimensional field corollary. This does not
settle LXXVI for algebras with nonzero projection-bearing quotients.
