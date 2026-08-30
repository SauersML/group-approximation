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

## New deductions recorded here

1. For every separable algebra, the LXXXI shadow hypothesis is equivalent to
   `ctdim(A)<=1`, where `ctdim` is the supremal spectrum dimension of its
   continuous-trace subquotients.  Morita equivalence supplies the reverse
   implication from a commutative hereditary shadow to the ideal it
   generates.
2. The invariant is a lower bound for nuclear dimension because nuclear
   dimension passes to subquotients and is computed by spectrum dimension on
   continuous-trace algebras.
3. The LXXXI shadow hypothesis forces every local continuous-trace spectrum
   chart to have dimension at most one, by cutting the compact-operator
   bundle with a local rank-one projection.  The fibre may be infinite
   dimensional and the bundle may have nontrivial Dixmier--Douady class.
4. Hence every separable continuous-trace algebra satisfying the hypothesis
   has nuclear dimension at most one.
5. Applying the same localization to every continuous-trace factor of a
   separable type-I composition series gives `topdim(A)<=1`.
6. Thus any remaining separable type-I counterexample must be a finite
   nuclear-dimension algebra with `topdim(A)<=1<dim_nuc(A)`.  This isolates
   the exact missing theorem: the one-dimensional type-I comparison between
   these two dimension theories.

No maximum formula for arbitrary extensions is assumed, and no universal
solution of Problem LXXXI is claimed.
