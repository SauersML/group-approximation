# STW LXXIV: property-SP and Cu-stability audit (2026-08-30)

## Problem boundary

Problem LXXIV asks whether a unital simple (optionally nuclear) C-star
algebra in which every nonzero projection is infinite must be purely
infinite.  Rordam posed the problem as Question 7.7 in *A simple C-star
algebra with a finite and an infinite projection*, Acta Math. 191 (2003),
109--142.  The primary manuscript is available at
<https://arxiv.org/abs/math/0204339>.  Schafhauser--Tikuisis--White still
list the problem as open in arXiv:2506.10902v2, including its addenda through
April 2026.

Targeted exact-phrase and concept searches through 2026-08-30 found no
primary source claiming a solution of the unrestricted problem.  This is a
literature screen, not proof that no unindexed result exists.

## Established literature boundary

1. Rordam's paper records the real-rank-zero positive case: for a simple
   algebra, real rank zero plus infiniteness of every nonzero projection is
   equivalent to pure infiniteness.  It also explains why his mixed finite
   and infinite examples do not decide Question 7.7.
2. Ortega--Perera--Rordam, *The Corona Factorization property, Stability,
   and the Cuntz semigroup of a C-star algebra*,
   <https://arxiv.org/abs/0903.2917>, proves the stability mechanism used in
   the new weak-omega route below.  In its notation, property (S) is
   equivalent (for separable algebras) to having neither a nonzero unital
   quotient nor a nonzero bounded lower-semicontinuous 2-quasitrace.  Their
   Proposition 4.8 says that a full hereditary subalgebra is stable under
   those conditions when the ambient Cuntz semigroup has weak
   omega-comparison and the stabilization contains a full projection.
3. Bonicke--Li, *Ideal structure and pure infiniteness of ample groupoid
   C-star algebras*, <https://arxiv.org/abs/1707.03740>, gives projection
   criteria for important ample-groupoid classes.  Those criteria use
   distinguished diagonal projections and do not settle arbitrary simple
   algebras.
4. Joan Bosa, *Stable Elements and Property (S)*,
   <https://arxiv.org/abs/2102.09442>, develops the regularity,
   asymptotic-regularity, property-R, and comparison framework around the
   same stability mechanism.  In particular its regularity dichotomies
   already imply related stably-finite-versus-purely-infinite positive
   classes.  Accordingly, the weak-omega positive conclusion below is not
   claimed as a new literature theorem.  What is new in this graph is its
   direct localization to the exact LXXIV projectionless corner, the
   elementary quasitrace elimination there, and the explicit orthogonal
   weak-omega failure witness forced by a counterexample.

No literature theorem in this artifact is represented as a solution of
LXXIV.  The imported implication in the weak-omega claim is the
Ortega--Perera--Rordam stability mechanism, with Bosa's later regularity
framework marking the known conceptual overlap.  The exact LXXIV-local
reduction and witness are written out in Cairn.

## New deductions

### Weak omega-comparison closes the hinge

If a separable LXXIV algebra were not purely infinite, its exact property-SP
reduction supplies a full projectionless hereditary algebra `D`.  The
stabilization of `D` contains the projection corresponding to the unit of
the original algebra, so `D` is not stable.  On the other hand, `D` has no
unital quotient and no bounded 2-quasitrace.  The latter assertion is
elementary: a nonzero bounded quasitrace on the simple algebra `D` is
faithful, its matrix extension evaluates a stabilized infinite projection,
and additivity on the equivalent range projection and its nonzero defect is
impossible.

Thus `D` has property (S).  Weak omega-comparison would force `D` to be
stable, a contradiction.  Consequently every separable counterexample
forces failure of weak omega-comparison.  The proof route also extracts a
concrete witness:

```text
x' << x,                    x <_s y_j for every j,
y_j full for every j,       x' not <= y_0+...+y_n for every n.
```

The `y_j` can be represented by pairwise orthogonal positive elements of the
same projectionless hereditary corner.

### Projectionless Morita normal form

A counterexample is equivalent to a sigma-unital simple projectionless
algebra `D` which is not purely infinite, whose stabilization contains a
nonzero projection, and whose every nonzero stabilized projection is
properly infinite.  Passing from a counterexample to `D` uses a
projectionless hereditary corner and Brown stabilization; the converse
takes any nonzero stabilized projection `p` and forms the unital corner
`p(D tensor K)p`.  This is an exact two-way normal form, not merely a list of
necessary conditions.

### Stationary matrix thresholds

For a nonzero positive `a` in the projectionless corner, let the matrix
projection threshold of a hereditary algebra `H` be the least `m` such that
`M_m(H)` contains a nonzero projection.  Compact fullness makes the
threshold finite.  Along a rapidly increasing sequence of spectral
cutdowns of `a`, the thresholds form a nonincreasing sequence of integers at
least two, hence are eventually constant.  At the stationary level every
nonzero projection is properly infinite and stably equivalent to the
original unit, while all lower matrix levels remain projectionless.

This normal form isolates a genuinely finite, locally stationary descent
failure: the remaining problem is not to create a projection at some matrix
level, but to lower a persistent minimal level `m>=2` to level one.

### Uniformly gapless scalar compression geometry

The stationary minimal level forces more than the existence of matrix
projections.  Choose one projection `p` at that level in the first hereditary
algebra of the stationary tail.  It then belongs to every later matrix
algebra.  No scalar rank-one compression of `p` can vanish: if the
compression in direction `xi` were zero, positivity gives
`p(xi tensor 1)=0`, and a scalar unitary moving `xi` to the last coordinate
would conjugate `p` into the preceding matrix level.  That contradicts
minimality.

The norm of the compression varies continuously over the compact unit sphere,
so all compressions have norm at least one fixed `delta>0`.  On the other
hand, every compression lies in the projectionless corner.  Functional
calculus therefore forces zero to be an accumulation point of its nonzero
spectrum.  Phase invariance packages the family as a continuous map

```text
CP^(m-1) -> D_+\{0}
```

whose image is uniformly bounded away from zero in norm but is pointwise
gapless at zero.  This sharpens the earlier gapless-compression observation:
there is no exceptional scalar direction with zero compression, and no
direction can supply the spectral gap needed for level-one projection
extraction.  The argument is internal and uses neither comparison nor
property (QQ).

### Algebraic Cuntz semigroups close the hinge

There is a comparison-free positive class not covered by the weak-omega or
almost-unperforation routes.  Under the LXXIV projection hypothesis,

```text
A is purely infinite  iff  Cu(A) is algebraic.
```

For the new direction, algebraicity puts a nonzero compact class below every
nonzero Cuntz class.  The standard compact-class realization theorem for
simple C-star algebras represents that class by a stabilized projection.
The LXXIV hypothesis makes this projection properly infinite; fullness then
makes its class equal to the unit class.  It follows that every nonzero Cuntz
class is the unit class, and in particular every nonzero hereditary
subalgebra contains a projection.  The converse is immediate because the
Cuntz semigroup of a unital purely infinite simple algebra has only zero and
the compact unit class.

The compact-class realization input is recalled explicitly in the
preliminaries of Andrew Toms, *Homotopies of constant Cuntz class*,
<https://arxiv.org/abs/2202.10428>, with the original references there.  No
classification, nuclearity, separability, real-rank, stable-rank, comparison,
or cancellation theorem enters the LXXIV-specific argument.

This also sharpens the counterexample obstruction.  A positive element in
the projectionless hereditary corner has a finite multiple equal to the unit
class, but its entire lower interval contains no nonzero compact element.
Thus every counterexample fails algebraicity at a single finite unit root.

### Property (QQ) exactly closes the finite-root hinge

Bosa's Definition 1.6 records property (QQ) for a Cuntz semigroup:

```text
m x properly infinite for some finite m  implies  x properly infinite.
```

This is precisely adapted to the internal finite-unit-root theorem but is
different from the earlier comparison and algebraicity hypotheses.  Under
the LXXIV projection hypothesis, every nonzero `x` satisfies
`m x=[1_A]` for some finite `m`, and the unit class is properly infinite.
Property (QQ) therefore makes `x` properly infinite.  Fullness gives
`[1_A]<=N x=x`, while the unit is the largest Cuntz class, so
`x=[1_A]`.  Thus the algebra is purely infinite.  The converse is immediate
from `Cu(A)={0,[1_A]}`.

This also gives a sharper obstruction.  Every nonzero class represented in
the full projectionless corner of a counterexample has a properly infinite
finite multiple but is not itself properly infinite: otherwise fullness
would identify it with the unit and put a nonzero projection back into that
corner.  Along the uniform spectral root towers, one fixed multiplicity
witnesses this failure at every compactly contained stage.  Hence a
counterexample does not merely fail a global comparison axiom; it exhibits
an entire localized tower on which proper infiniteness fails to descend
through finite roots.

### Z-stability and finite nuclear dimension close the comparison hinge

Rordam's Theorem 4.5 in *The stable and the real rank of Z-absorbing
C*-algebras*, <https://arxiv.org/abs/math/0408020>, proves that Z-stability
forces almost unperforation of the Cuntz semigroup.  Applying it after
stabilization gives almost unperforation of `Cu(A)`.  The already established
unit-level almost-unperforation theorem therefore yields

```text
simple + unital + Z-stable + LXXIV projection hypothesis
    => purely infinite.
```

This is a corollary of the existing Cuntz-semigroup hinge, not a second proof
of it.

There is a useful finite-dimensional-regularity consequence.  Winter,
*Nuclear dimension and Z-stability of pure C*-algebras*,
<https://arxiv.org/abs/1006.2731>, proves that a separable simple unital
non-elementary C*-algebra of finite nuclear dimension is Z-stable.  The
non-elementary qualification is automatic here: a simple unital elementary
C*-algebra is a matrix algebra, and its rank-one projections are finite, in
direct conflict with the LXXIV hypothesis.  Hence

```text
separable + simple + unital + finite nuclear dimension
    + LXXIV projection hypothesis
    => purely infinite.
```

In particular, every separable counterexample has infinite nuclear dimension
and is non-Z-stable.  The latter conclusion holds even without separability.
Neither obstruction supplies property (SP) for an arbitrary non-Z-stable
algebra, so the unrestricted problem remains open.
