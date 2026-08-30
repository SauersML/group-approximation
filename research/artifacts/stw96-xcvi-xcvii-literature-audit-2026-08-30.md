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
