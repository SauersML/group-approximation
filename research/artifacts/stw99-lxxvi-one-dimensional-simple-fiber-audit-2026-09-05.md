# One-dimensional bases with arbitrary K1: graph-limit audit

## Result

Let `D` be simple, separable, and stably finite. Suppose `D` and
`D tensor Z` have stable rank one, and the actual first-factor map
induces an isomorphism on Cu. Then `C_0(X,D)` is Cu-regular for every
second-countable locally compact Hausdorff space `X` of covering dimension
at most one. In particular this holds for simple separable stably finite
pure `D`, and the resulting function algebra is also pure.

This extends the finite-graph compact-core theorem using permanence. It
does not extend the finite-core classification formula to infinite graphs
or arbitrary one-dimensional compacta.

## Compact bases

A compact second-countable Hausdorff space is metrizable. The
one-dimensional case of the Freudenthal polyhedral representation theorem
gives an inverse sequence of finite graphs with surjective bonding maps

```text
X = lim_inverse (X_n, r_n).
```

Allow disconnected finite graphs, including isolated vertices, so the
statement also includes dimension zero. The pullback homomorphisms give

```text
C(X,D) = lim_direct (C(X_n,D), r_n^* tensor id_D).
```

This identity can be checked before tensoring: cylinder functions form a
selfadjoint unital separating subalgebra of `C(X)`, hence are uniformly
dense. Finite sums of such scalar functions times coefficient elements
are dense in `C(X,D)`. The first-factor maps at each stage commute with
the connecting maps, so their inductive-limit map is the actual
first-factor map of `C(X,D)`.

The scalar inclusion into `Z` induces the K1 isomorphism for the coefficient
first-factor map. The finite-graph compact-core theorem therefore makes
each stage Cu-regular. Cu preserves sequential inductive limits; the
natural diagram of stage isomorphisms yields an isomorphism at the limit.
Equivalently, apply the existing inductive-limit permanence theorem for
concrete Cu regularity.

The precise topological representation and this C*-algebra/Cu limit
passage already appear in the proof of Antoine--Perera--Santiago,
Theorem 3.4, page 17 of arXiv:1101.4776. Their coefficient K1-vanishing
assumption is needed for their finite-stage pointwise formula. The
topological approximation and continuity argument do not use it. Here
the finite-stage input is the actual first-factor isomorphism proved by
the compact-core argument.

## Locally compact bases

If `X` is noncompact, let `X^+=X union {infinity}` be its one-point
compactification. Since `X` is locally compact, Hausdorff, and second
countable, it is sigma-compact and metrizable, and `X^+` is compact
metrizable. Take a compact exhaustion `X=union_n L_n`. The subsets
`L_n` and the singleton at infinity are closed in `X^+`, and each has
dimension at most one. The countable closed-sum theorem for covering
dimension of metric spaces therefore gives `dim(X^+)<=1`.

The compact result applies to `C(X^+,D)`. The algebra `C_0(X,D)` is its
closed two-sided ideal consisting of sections vanishing at infinity.
Concrete Cu regularity passes to ideals, so `C_0(X,D)` is Cu-regular.
The compatibility of this ideal with the target is literal:

```text
C_0(X,D) tensor Z = C_0(X,D tensor Z)
                 = ker(ev_infinity:C(X^+,D tensor Z)->D tensor Z).
```

This is the same compactification reduction used in the last paragraph
of the proof of APS Theorem 3.4. It does not require an extension
permanence theorem in the reverse direction.

## Scope

Simple stably finite pure coefficients satisfy the coefficient hypotheses
by the simple-case concrete Cu theorem and stable rank one. The
continuous-function purity theorem separately supplies purity of the
resulting `C_0(X,D)`.

The base may have infinite branching, infinitely many circles, or may fail
to be a graph. Arbitrary coefficient K1 and nonzero projections are
allowed. The output is still an isomorphism of the actual first-factor
Cu map, not an assertion that ranks determine all classes. Already on a
single circle, nonzero K1 in a projection corner produces compact
clutching data invisible to point evaluation.

Neither the finite-graph theorem nor this limit corollary solves STW
LXXVI for arbitrary pure C*-algebras. General nonsimple coefficients and
higher-dimensional function-algebra bases remain outside this result.

## Primary sources

- Antoine--Perera--Santiago,
  [Pullbacks, C(X)-algebras, and their Cuntz semigroup](https://arxiv.org/abs/1101.4776),
  proof of Theorem 3.4, for graph approximation, Cu continuity, and the
  compactification reduction.
- Coward--Elliott--Ivanescu,
  [The Cuntz semigroup as an invariant for C*-algebras](https://doi.org/10.1016/j.jreineangew.2007.10.008),
  Theorem 2 for sequential continuity.
- Seth--Vilalta,
  [Continuous functions over a pure C*-algebra](https://arxiv.org/abs/2602.14809),
  for purity in the simple-pure-fiber corollary.
