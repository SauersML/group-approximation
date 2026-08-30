# STW XCVI: mixed real-rank-zero extension audit (2026-08-30)

## Scope and conclusion

This audit targets the surviving finite-nuclear-dimension,
nowhere-scattered, real-rank-zero case in which the algebra has a nonzero
purely infinite simple subquotient but is not itself purely infinite.  The
mixed case is not intrinsically an obstruction: every such algebra with
finitely many ideals, and more generally every such algebra admitting a
continuous ordinal composition series, has generator rank one.

The useful operation is to glue `Z`-stability along the ideal filtration and
invoke real rank zero only after the gluing is complete.  Trying to glue
generators directly loses too much dimension.

## Primary inputs checked

* Hannes Thiel, [*The generator rank of C*-algebras*](https://arxiv.org/abs/1210.6608),
  Theorems 6.2--6.3 in the published numbering, proves
  `max(gr(I),gr(A/I)) <= gr(A) <= gr(I)+gr(A/I)+1`.  Thus generator rank one
  for both layers yields only the upper bound three for the extension.
* Andrew Toms and Wilhelm Winter, [*Strongly self-absorbing
  C*-algebras*](https://arxiv.org/abs/math/0502211), Corollary 3.4 and Theorem
  4.3, prove permanence of `D`-stability under sequential inductive limits and
  extensions of separable C*-algebras when `D` is strongly self-absorbing and
  `K_1`-injective.  Their Section 1 records these properties for `Z`.
* Aaron Tikuisis, [*Nuclear dimension, Z-stability, and algebraic simplicity
  for stably projectionless C*-algebras*](https://arxiv.org/abs/1210.2237),
  Corollary 8.7, states exactly that a separable finite-nuclear-dimension
  C*-algebra with finitely many ideals and no elementary ideal-quotient is
  `Z`-stable.  Its proof is the finite successor-extension induction used
  here.  The simple nonunital case is included.
* Hannes Thiel, [*Generators in Z-stable C*-algebras of real rank
  zero*](https://arxiv.org/abs/2006.08404), Theorem 5.3, proves that every
  separable `Z`-stable real-rank-zero C*-algebra has generator rank one,
  including the nonunital case.
* Hannes Thiel and Eduard Vilalta, [*Nowhere scattered
  C*-algebras*](https://arxiv.org/abs/2112.09877), Theorem 3.1, identifies
  nowhere scatteredness with the absence of nonzero elementary
  ideal-quotients.

The literature search was refreshed through 2026-08-30.  The 2025 Global
Glimm theorem strengthens the divisibility corridor but does not supply a
generator-rank extension theorem.  No 2025--2026 primary result found in the
search removes the ideal-filtration boundary below.

## New reduction

For a continuous filtration indexed by an arbitrary ordinal, successor stages
are handled by extension permanence of `Z`-stability.  A limit of countable
cofinality is a sequential inductive limit, so Corollary 3.4 applies.  At a
limit of uncountable cofinality, separability forces actual stabilization:
choose approximants at every precision to a countable dense set, and the
supremum of their stage indices is still below the limit ordinal.  The limit
ideal therefore equals one earlier ideal.  Transfinite induction makes the
total algebra `Z`-stable, and real rank zero lets Thiel's theorem give
generator rank one.

In the nowhere-scattered finite-nuclear-dimension setting, every simple layer
is non-elementary and of finite nuclear dimension, hence `Z`-stable by
Tikuisis.  Purely infinite and stably finite layers may alternate arbitrarily;
their type does not enter the induction.

## Exact remaining boundary

Any counterexample in the finite-nuclear-dimension, nowhere-scattered,
real-rank-zero class must have infinitely many ideals and must fail to admit a
continuous ordinal composition series by simple subquotients.  In
particular, merely inserting a purely infinite simple subquotient into a
finite extension cannot produce a counterexample.

This is a reduction, not a solution of the unrestricted real-rank-zero
problem.  We do not assert that every separable primitive ideal space admits
such a composition series, nor that generator rank one itself is extension
permanent.
