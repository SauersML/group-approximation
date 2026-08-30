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
