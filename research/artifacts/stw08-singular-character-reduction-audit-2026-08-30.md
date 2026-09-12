# STW Problem VIII: singular-character reduction audit (2026-08-30)

## Result

Problem VIII is equivalent to its restriction to nonzero separable unital
exact quasidiagonal algebras `E` with a character whose kernel is stable and
essential.  Moreover, every counterexample produces one for which the
character is the unique tracial state and the stable kernel has no bounded
trace but does have a nontrivial unbounded lower-semicontinuous tracial
weight.

The construction is canonical:

```text
A |-> E=(A tensor K)~.
```

## AF-embedding equivalence

This reduction requires more than the usual permanence of
quasidiagonality.  If `A->F` is an AF embedding, tensoring with `K` and then
unitizing embeds `E` into the AF algebra `(F tensor K)~`.  In the reverse
direction, `A` is the corner `A tensor e_11` inside `E`, and AF-embeddability
passes to C-star subalgebras.  Hence `A` and `E` are AF-embeddable
simultaneously.

Tensoring an injective map with `K` is injective because `K` is nuclear;
the unitized map remains injective because its restriction to the ideal is
injective and its scalar quotient is the identity.  Stabilizations and
unitizations of AF algebras are AF.

## Trace pinning

Every bounded trace on a stable algebra vanishes.  The proof uses arbitrarily
many multiplier isometries with orthogonal ranges and gives, for every
positive `a`,

```text
m rho(a) <= ||rho|| ||a||.
```

Thus all tracial states of `E` factor through the scalar quotient, making
the quotient character unique.  It is automatically a quasidiagonal trace
but is nonfaithful.  This places the normal form exactly outside Problem
IX(2), whose hypothesis is a faithful quasidiagonal trace.

If the kernel were traceless, Gabe's Theorem C would turn its exact
quasidiagonality into an AF embedding, and unitization would embed `E` as
well.  A counterexample kernel must therefore admit a lower-semicontinuous
tracial weight taking a finite nonzero value.  The preceding stable-algebra
calculation shows that it cannot be bounded.

## Novelty and boundary

The stabilization/unitization device also appears in the repository's
Problem VII analysis, but the invariant being reflected here is different:
AF-embeddability rather than quasidiagonality.  Equality `(SC1)` is what
makes this an exact reduction of Problem VIII.

The theorem does not construct a counterexample and does not solve the
remaining stable-kernel case.  It rules out two tempting proof partitions:
neither the faithful bounded trace theorem nor the traceless theorem can
settle the reduced case.  Any full proof must control an unbounded tracial
weight on a stable exact quasidiagonal ideal, or bypass it by producing the
missing coherent finite-dimensional system directly.
