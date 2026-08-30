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

[Li--Niu--Ruzicka, *Villadsen algebras are singly
generated*](https://arxiv.org/abs/2604.07688), published online first in JNCG
in 2026, proves that every simple unital AH algebra with diagonal maps is singly
generated, and more generally that tensoring an algebra with their AF-action by
an arbitrary separable unital C*-algebra preserves single generation.  Their
Villadsen algebras are explicitly of the first type.  The Elliott--Li--Niu
counterexample is of the second type and its connecting maps carry nontrivial
bundle corners, so it is outside that theorem rather than contradicting it.

Curda--Gonzales--Wu also point out the exact higher-rank boundary: a higher-rank
graph algebra can be `C(T^k)`, so their directed-graph theorem cannot extend to
all higher-rank graph algebras.  These were the only 2026 primary single-
generation results located through 2026-08-30 besides the Elliott--Li--Niu
counterexample.

## New closure and normal-form consequences

The finite obstruction in Elliott--Li--Niu is functorial in the useful
direction.  If `q:E -> A` is onto and `F_tilde` is any set of lifts of their
fixed finite set `F`, then a containment

```text
F_tilde subset C*(g)
```

would give `F subset C*(q(g))`, a contradiction.  Thus the strong obstruction,
not just failure of single generation, lifts through every quotient map.

Combining this observation with Thiel--Vilalta, *Nowhere scattered
C*-algebras*, Theorem 3.1 and Proposition 4.2, gives two unconditional closure
theorems recorded in the graph:

* every extension of the Elliott--Li--Niu algebra by a nowhere-scattered ideal
  is nowhere scattered and not singly generated;
* a unital `C(X)`-algebra whose fibres are all nowhere scattered is nowhere
  scattered, and one fibre carrying a finite generator obstruction forces the
  total algebra to carry the lifted obstruction.

The fibre statement follows because every irreducible representation of a
unital `C(X)`-algebra has a central character `x`, factors through `E_x`, and is
therefore non-GCR when that fibre is nowhere scattered.  Theorem 3.1(6) then
gives nowhere scatteredness of the total algebra.

In particular, for every nonempty compact metrizable `X`,

```text
C(X) tensor_min A
```

is a unital separable nuclear nowhere-scattered counterexample.  It has centre
exactly `C(X)` and is non-simple for every non-singleton `X`.  This is a
counterexample normal form with freely prescribed compact metrizable central
base, including connected bases, rather than a mere direct-sum enlargement.

## Logical relationship between the two parts of XCVI

The general nowhere-scattered conjecture would have implied the simple
conjecture.  A unital simple infinite-dimensional algebra is nowhere scattered
by Thiel--Vilalta, Example 3.2, and every finite-dimensional simple algebra is a
matrix algebra and is singly generated.  The reverse implication is not a
formal reduction: non-simple nowhere-scattered algebras are not controlled by a
claim about simple algebras, and single generation does not pass to extensions.
The Elliott--Li--Niu example happens to refute both because it lies in the
overlap (simple, infinite-dimensional, hence nowhere scattered).  The new
`C(X)` family shows that the general negative answer also has genuinely
non-simple representatives.

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
