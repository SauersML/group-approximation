# STW LXXXI: continuous-trace and type-I frontier audit

Date: 2026-08-30

## Current-status screen

The source problem remains open in general.  Searches of current primary
literature through the date above found no general solution and no theorem
identifying nuclear dimension with Brown--Pedersen topological dimension for
all type-I C-star algebras.  The relevant established inputs are:

- Winter--Zacharias,
  [*The nuclear dimension of C-star algebras*](https://arxiv.org/abs/0903.4914),
  Corollary 2.10: nuclear dimension of a separable continuous-trace algebra
  equals the covering dimension of its spectrum.
- Hannes Thiel,
  [*The topological dimension of type I C-star algebras*](https://arxiv.org/abs/1210.4314),
  for the composition-series behavior of Brown--Pedersen topological
  dimension.  The current revision explicitly says that its exact relation
  to nuclear dimension is unclear.
- Samuel Evington,
  [*Nuclear dimension of extensions of O-infinity-stable algebras*](https://arxiv.org/abs/2012.03650),
  Theorem 1: a full extension with separable stable ideal `J` and separable
  nuclear O-infinity-stable quotient has nuclear dimension between one and
  `dim_nuc(J)+1`.  Fullness means that the Busby image of every nonzero
  element is norm-full in the corona; in particular, unital extensions with
  simple quotient are full.

## New deductions recorded here

1. For every separable algebra, the LXXXI shadow hypothesis is equivalent to
   `ctdim(A)<=1`, where `ctdim` is the supremal spectrum dimension of its
   continuous-trace subquotients.  Morita equivalence supplies the reverse
   implication from a commutative hereditary shadow to the ideal it
   generates.
2. The invariant is a lower bound for nuclear dimension because nuclear
   dimension passes to subquotients and is computed by spectrum dimension on
   continuous-trace algebras.
3. Unlike nuclear dimension, `ctdim` satisfies the exact maximum formula
   across every separable extension.  A continuous-trace subquotient of the
   middle algebra decomposes into an open-spectrum subquotient of the ideal
   and a closed-spectrum subquotient of the quotient; countable stability of
   metric covering dimension supplies the maximum.
4. The Rieffel ideal correspondence shows that `ctdim` is strongly Morita
   invariant.  Hence the LXXXI shadow hypothesis is itself Morita invariant
   in the separable setting and may be tested after stabilization.
5. On separable type-I algebras, `ctdim` is exactly Brown--Pedersen
   topological dimension: one inequality comes from arbitrary
   continuous-trace subquotients, and the other from a continuous-trace
   composition series.
6. A hypothetical separable counterexample can be stabilized or unitized
   without changing its finite nuclear dimension or losing the shadow
   hypothesis.  This removes two artificial search frontiers.
7. The LXXXI shadow hypothesis forces every local continuous-trace spectrum
   chart to have dimension at most one, by cutting the compact-operator
   bundle with a local rank-one projection.  The fibre may be infinite
   dimensional and the bundle may have nontrivial Dixmier--Douady class.
8. Hence every separable continuous-trace algebra satisfying the hypothesis
   has nuclear dimension at most one.
9. Applying the same localization to every continuous-trace factor of a
   separable type-I composition series gives `topdim(A)<=1`.
10. Thus any remaining separable type-I counterexample must be a finite
   nuclear-dimension algebra with `topdim(A)<=1<dim_nuc(A)`.  This isolates
   the exact missing theorem: the one-dimensional type-I comparison between
   these two dimension theories.
11. The invariant is exactly continuous under countable increasing
    hereditary exhaustions:
    `ctdim(closure(union_n B_n))=sup_n ctdim(B_n)`.  Hence the LXXXI shadow
    hypothesis is preserved and reflected by sequential inductive limits
    with injective hereditary-image connecting maps.  The proof cuts every
    continuous-trace subquotient by the stage hereditary algebras, passes to
    the generated open-spectrum ideals, and applies the metric countable
    closed-sum theorem.
12. There is a genuinely non-type-I positive extension class which does not
    rely on Problem LXXXII.  If the extension is full, the ideal is separable
    stable AF, and the nonzero quotient is separable nuclear and
    O-infinity-stable, Evington's estimate reads
    `1<=dim_nuc(A)<=dim_nuc(J)+1=1`.  Therefore `dim_nuc(A)=1`, while the
    general lower bound `ctdim(A)<=dim_nuc(A)` makes the LXXXI shadow
    hypothesis automatic.  Toeplitz--Cuntz algebras supply concrete
    non-type-I examples: their ideal is `K`, their quotient is the simple
    O-infinity-stable algebra `O_n`, and unitality plus simplicity gives
    fullness.

No maximum formula for arbitrary extensions is assumed, and no universal
solution of Problem LXXXI is claimed.  No continuity statement for
arbitrary injective inductive systems is claimed.  The full-extension class
uses Evington's theorem only under its stated stability, fullness, and
O-infinity-stability hypotheses; it does not assert color collapse for a
general extension.
