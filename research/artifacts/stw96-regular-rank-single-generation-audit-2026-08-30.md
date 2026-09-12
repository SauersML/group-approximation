# STW XCVI surviving regular-rank frontiers: audit and reductions

Date: 2026-08-30.

## Current boundary

Elliott--Li--Niu's August 2026 example settles the unrestricted simple and
nowhere-scattered questions negatively, but it does not settle either surviving
regularity variant.  Their Proposition 3.3 gives

```text
2 <= tsr(A) <= 4,       2 <= rr(A) <= 3,
```

and Remark 3.4 asks whether simple separable stable-rank-one algebras, or
separable real-rank-zero algebras, are singly generated.  No later primary
result through 2026-08-30 resolves either question.

The other 2026 single-generation papers do not close this gap:

* Li--Niu--Ruzicka, [*Villadsen algebras are singly
  generated*](https://arxiv.org/abs/2604.07688), cover simple unital AH
  algebras with diagonal maps, including first-type Villadsen algebras of
  stable rank one.  The Elliott--Li--Niu second-type construction is outside
  the diagonal-map hypothesis.
* Curda--Gonzales--Wu, [*Graph C*-algebras are singly
  generated*](https://arxiv.org/abs/2601.01249), cover every countable directed
  graph algebra, but not arbitrary real-rank-zero or stable-rank-one algebras.

## Quotient regularization firewall

Stable rank one, real rank zero, nowhere scatteredness, and single generation
all pass to quotients.  Therefore any obstruction transferred from a quotient
already requires a seed counterexample in the desired regularity class.  In
particular, every algebra surjecting onto the Elliott--Li--Niu example has
stable and real rank at least two.

This rules out the entire quotient-detected family from the previous XCVI wave:

* extensions with quotient the Elliott--Li--Niu algebra;
* `C(X)`-algebras having it as a fibre;
* `A tensor D` when `D` has a character, using `id tensor chi`.

The firewall is exact rather than heuristic.  A tensor factor without a
character avoids the quotient, but then the obstruction has not been
transferred.  Standard regularizing factors illustrate the danger: UHF
absorption and `Z`-absorption are themselves positive single-generation
mechanisms.

## A new positive real-rank-zero corridor

Two primary results combine to give a useful unconditional class not previously
recorded in this graph.

First, Ng--Thiel--Vilalta, [*The Global Glimm Property for C*-algebras of
topological dimension zero*](https://doi.org/10.1112/blms.70343), Theorem 2.3,
show that topological-dimension-zero algebras are nowhere scattered exactly when
they have the Global Glimm Property.  Real rank zero implies the ideal property,
which implies topological dimension zero.  Hence every real-rank-zero
nowhere-scattered algebra already has almost-full square-zero elements in every
hereditary subalgebra.

Second, Robert--Tikuisis, [*Nuclear dimension and Z-stability of non-simple
C*-algebras*](https://arxiv.org/abs/1308.2941), Corollary 7.11, imply that a
separable finite-nuclear-dimension algebra is `Z`-stable when it has no
elementary subquotients, no purely infinite simple subquotients, and a
compact-open basis for its primitive ideal space.  Nowhere scatteredness gives
the first condition and real rank zero gives the third.  Hannes Thiel,
[*Generators in Z-stable C*-algebras of real rank
zero*](https://arxiv.org/abs/2006.08404), Theorem 5.3, then gives generator rank
one.  Its Corollary 5.5 separately gives generator rank one for every nuclear,
purely infinite real-rank-zero algebra, with no finite-dimensionality
assumption.

Consequently:

```text
RR0 + nowhere scattered + finite nuclear dimension
    + no purely infinite simple subquotient
        => Z-stable => generator rank one.
```

Robert--Tikuisis explicitly verify the middle structural hypotheses for finite
decomposition rank plus the ideal property.  Thus every separable
real-rank-zero nowhere-scattered algebra of finite decomposition rank has a
dense `G_delta` set of generators.

## Exact open residue

The Global Glimm Property alone does not provide the approximately central,
commuting coding used in the known generator theorems.  The argument above
therefore stops at the following honest boundary:

* the simple stable-rank-one question remains open outside the known
  `Z`-stable, diagonal AH, graph, and related classes;
* a real-rank-zero nowhere-scattered counterexample must escape finite
  decomposition rank;
* within finite nuclear dimension, the Robert--Tikuisis route leaves only
  algebras having a nonzero purely infinite simple subquotient; Thiel's
  Corollary 5.5 further excludes algebras which are themselves purely infinite,
  so any counterexample there would have a purely infinite simple subquotient
  while the total algebra is not purely infinite;
* quotient, retract, character-tensor, and obstructed-fibre transfers of the
  Elliott--Li--Niu example cannot enter either regularity class.

No conditional construction or open witness is promoted here.
