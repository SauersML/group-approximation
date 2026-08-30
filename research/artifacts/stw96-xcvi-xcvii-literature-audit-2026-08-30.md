# STW Problems XCVI/XCVII: post-publication audit

Date: 2026-08-30.

## Resolution found

The post-April-2026 preprint
[Elliott--Li--Niu, *A simple separable C*-algebra which is not singly
generated*](https://arxiv.org/abs/2608.13707), submitted 2026-08-13, proves:

```text
There is a simple unital separable AH algebra A such that
C*(1,g) != A for every g in A.
```

This is Theorem 1.1, strengthened in Theorem 3.1 to the existence of a fixed
finite set contained in no singly generated subalgebra.  Since AH algebras are
nuclear, it gives a negative answer to Problem XCVII as well as the first part
of Problem XCVI.  Since the example is simple and infinite-dimensional, it is
nowhere scattered, so it also refutes XCVI's general formulation.

The proof was checked against the v1 PDF, not only the abstract.  Its decisive
obstruction is the incompatibility between a nonzero Thom--Porteous homology
class on the zero locus of the generator's off-diagonal corner and the
vanishing of degree-at-least-two homology for the planar spectrum through
which a scalar one-generator corner must factor.

## Other post-April result

[Curda--Gonzales--Wu, *Graph C*-algebras are singly
generated*](https://arxiv.org/abs/2601.01249), published online 2026-07-29,
proves single generation for all countable graph C*-algebras.  This is a broad
positive subclass but does not conflict with the AH counterexample.

## Unital countably layered positive class

The extension and limit permanence of Z-absorption yields a broader XCVII
positive class than the previously recorded real-rank-zero theorem.  If a
unital separable algebra has a continuous ideal filtration indexed by a
countable ordinal and every successor quotient is Z-stable, then Toms--Winter
extension permanence and inductive-limit permanence make the total algebra
Z-stable.  Thiel--Winter's unital coding theorem then gives one generator.
Real rank zero is not used; unlike the real-rank-zero theorem, this argument
asserts existence and not density of generators.

For a concrete nuclear consequence, suppose the total algebra is nowhere
scattered and has finite nuclear dimension, and the successor quotients are
simple.  Each layer is then non-elementary and has finite nuclear dimension,
so Tikuisis, Corollary 8.7, makes it Z-stable.  Hence every unital separable
nowhere-scattered finite-nuclear-dimension algebra with finitely many ideals
is singly generated.  The one-layer case says that every non-elementary
unital simple separable finite-nuclear-dimension algebra lies in the positive
region of XCVII.

The trust boundary is exact: single generation itself is not asserted to pass
through extensions.  Z-absorption is glued first, and unitality is used only
when applying Thiel--Winter to the total algebra.  No generator-rank-one
statement is inferred without real rank zero.

## Remaining frontier

The counterexample has neither stable rank one nor real rank zero:

```text
2 <= tsr(A) <= 4,       2 <= rr(A) <= 3.
```

Accordingly, the following are still open and are recorded as separate roots:

* whether every unital simple separable stable-rank-one C*-algebra is singly
  generated;
* whether every separable real-rank-zero C*-algebra is singly generated.

For nuclear algebras, Z-stability remains a sufficient condition by
Thiel--Winter, but it is no longer a plausible answer to Problem XCVII itself:
the Elliott--Li--Niu AH example is nuclear and non-Z-stable.

## Source status

arXiv:2608.13707 is presently a v1 preprint rather than a peer-reviewed
publication.  The graph records the theorem with that provenance and does not
upgrade its publication status.
