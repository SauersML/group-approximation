# STW XCVI: local fibre gluing audit (2026-08-30)

## Outcome

The finite-nuclear-dimension, nowhere-scattered, real-rank-zero generator
problem has a local-to-global solution whenever the primitive ideal space is
locally Hausdorff.  This removes ideal spaces with perfect, non-scattered
Hausdorff pieces and does not require a composition series.

The same proof applies layerwise to a continuous ordinal ideal filtration
whose successor quotients have locally Hausdorff primitive spectra.  Thus the
total primitive space may itself be non-locally-Hausdorff.

The argument combines three scales:

1. real rank zero makes every Hausdorff open piece zero-dimensional;
2. fibrewise `Z`-stability makes the ideal over that piece `Z`-stable; and
3. a countable open cover is glued by sums of ideals and an inductive limit.

## Primary-source audit

* Hirshberg--Rordam--Winter, [*C_0(X)-algebras, stability and strongly
  self-absorbing C*-algebras*](https://arxiv.org/abs/math/0610344), Theorem
  4.6, has the exact needed hypotheses: `D` is `K_1`-injective and strongly
  self-absorbing, `X` is locally compact metrizable of finite covering
  dimension, and the `C_0(X)`-algebra is separable.  It concludes that the
  total algebra is `D`-stable exactly when every fibre is.  We use `D = Z` and
  covering dimension zero.
* Toms--Winter, [*Strongly self-absorbing
  C*-algebras*](https://arxiv.org/abs/math/0502211), Corollary 3.3,
  Corollary 3.4, and Theorem 4.3 give quotient, sequential-inductive-limit,
  and extension permanence of `Z`-stability.
* Tikuisis, [*Nuclear dimension, Z-stability, and algebraic simplicity for
  stably projectionless C*-algebras*](https://arxiv.org/abs/1210.2237),
  Corollary 8.7, includes the simple nonunital finite-nuclear-dimension case
  once elementary ideal-quotients are excluded.
* Thiel--Vilalta, [*Nowhere scattered
  C*-algebras*](https://arxiv.org/abs/2112.09877), Theorem 3.1, supplies that
  exclusion.  Thiel, [*Generators in Z-stable C*-algebras of real rank
  zero*](https://arxiv.org/abs/2006.08404), Theorem 5.3, converts the glued
  `Z`-stability into generator rank one.

The search was refreshed through 2026-08-30.  No later primary result found in
the search removes the non-locally-Hausdorff boundary.  The 2024 inverse
primitive-space theorem shows that primitive spaces of separable nuclear
C*-algebras can be substantially more singular than locally Hausdorff, so this
boundary is genuine rather than automatic.

## Why the cover gluing is sound

For a Hausdorff open set `U`, the corresponding ideal has primitive spectrum
`U`.  Real rank zero supplies a compact-open basis, and separability makes `U`
second countable, hence a zero-dimensional locally compact metrizable base.
Hausdorffness makes every point closed, so the Dauns--Hofmann fibres are
simple ideal-quotients.  The fibrewise theorem applies.

If `(U_n)` is a countable Hausdorff-open cover and `B_n` are the corresponding
ideals, finite sums are `Z`-stable because

`(J + B)/J = B/(B intersect J)`

is a quotient of a `Z`-stable ideal and extension permanence applies.  The
finite sums increase densely to the ideal corresponding to `union U_n`, which
is all of `A`; inductive-limit permanence completes the proof.

## Exact residue

Any counterexample among separable nowhere-scattered finite-nuclear-dimension
real-rank-zero C*-algebras must now have a primitive ideal space that is not
locally Hausdorff.  More sharply, it cannot admit a continuous ordinal ideal
filtration whose successor quotients have locally Hausdorff primitive spectra.
In particular, it has infinitely many ideals and no continuous ordinal
composition series with simple successor quotients.  At limits of uncountable
cofinality, separability forces the ideal filtration to stabilize; only
countable-cofinality limits require inductive-limit permanence.

We do not claim that every zero-dimensional primitive ideal space is locally
Hausdorff.  A compact-open basis in a non-Hausdorff `T_0` space does not provide
Hausdorff neighborhoods, and the fibrewise `C_0(X)` theorem cannot be applied
directly to such a piece.
