# Problem LXXII: purely infinite radical and quotient-seed audit (2026-08-30)

## Result

Every C-star algebra has a largest purely infinite ideal

```text
P_pi(A)=closure(sum{I ideal in A : I is purely infinite}).
```

For weakly purely infinite `A`, the quotient `A/P_pi(A)` is weakly purely
infinite and contains no nonzero purely infinite ideal.  Thus every possible
counterexample has a canonical quotient all of whose nonzero ideals are
themselves counterexamples.  As a positive consequence, weak pure
infiniteness collapses whenever every nonzero quotient contains a nonzero
chain-ideal ideal.

## Permanence audit

The radical proof uses the same three Kirchberg--Rordam permanence inputs
already isolated and audited in the chain-cover proof.

1. A quotient of a purely infinite C-star algebra is purely infinite.
2. An extension with purely infinite ideal and quotient is purely infinite.
3. A directed C-star inductive limit of purely infinite algebras is purely
   infinite.

For two purely infinite ideals `I,J`, the exact sequence

```text
0 -> I -> I+J -> J/(I intersect J) -> 0
```

first proves that `I+J` is purely infinite.  Finite sums are therefore
purely infinite, and their directed limit is exactly the closed sum defining
`P_pi(A)`.  No closure of an algebraic infinite sum is silently assumed,
and no permanence assertion for intersections is used.

If `K` is a purely infinite ideal in `A/P_pi(A)`, its inverse image is an
extension of `K` by `P_pi(A)` and hence is a purely infinite ideal larger
than the radical.  This contradiction proves that the quotient is
radical-free.  Weak pure infiniteness passes to both ideals and quotients,
so every nonzero ideal in a counterexample's radical-free quotient remains
weakly purely infinite and cannot be purely infinite.

Because every ideal of a weakly purely infinite algebra is weakly purely
infinite, Kirchberg--Rordam's equivalence

```text
purely infinite  iff  weakly purely infinite + Global Glimm Property
```

identifies `P_pi(A)` with the closed sum of all Global Glimm ideals and, by
the proof above, with the largest Global Glimm ideal.  Thus the residual
quotient has no nonzero Global Glimm ideal.  Each of its nonzero ideals is
again weakly purely infinite and hence nowhere scattered.  Thiel--Vilalta's
characterization then forces the Cuntz semigroup of every such ideal to
fail ideal-filteredness or property (V).  This is a hereditary algebraic
form of the exact remaining obstruction, not only a statement about the
primitive topology.

## Exact obstruction and boundary

The general weak-to-plain problem is equivalent to the radical-free case.
This is not a proposed counterexample and does not prove that a nonzero
radical-free weakly purely infinite algebra exists.  It says precisely what
one would have to look like.

For `B=A/P_pi(A)` arising from a counterexample:

* `Prim(B)` has no isolated point, since an isolated point supplies a
  nonzero simple ideal, and a simple weakly purely infinite ideal is purely
  infinite;
* no nonempty open subset of `Prim(B)` is topologically scattered;
* no nonzero ideal of `B` has a chain, finite, scattered, chain-covered, or
  continuous simple-layer ideal geometry covered by the established LXXII
  theorems;
* no nonzero ideal of `B` has the Global Glimm Property, and each such
  ideal's Cuntz semigroup fails ideal-filteredness or property (V);
* every nonempty open subset corresponds to another weakly-but-not-plain
  purely infinite algebra.

This firewall reaches beyond the finite/scattered positive classes: it
removes all purely infinite open patches simultaneously and makes the
remaining obstruction hereditary under passage to nonzero open ideals.

## Quotient-seed theorem

Suppose every nonzero quotient `A/I` contains a nonzero ideal `J/I` whose
own ideal lattice is a chain.  Apply this only once, to the canonical
radical-free quotient.  The chain theorem makes `J/I` purely infinite,
contradicting radical-freeness.  Therefore the quotient is zero and `A` is
purely infinite.

Topologically, this says every nonempty closed subspace of `Prim(A)` has a
nonempty relatively open chain subspace.  Unlike the chain-cover theorem,
the good patch is allowed to appear only after quotienting; unlike the
scattered theorem, it can be an infinite chain spectrum with no isolated
point.  The theorem does not claim that this condition holds for every
primitive spectrum—the radical-free quotient isolates exactly the case in
which it fails.

The permanence inputs are those of E. Kirchberg and M. Rordam,
*Non-simple purely infinite C-star algebras*, American Journal of
Mathematics 122 (2000), 637--666, DOI `10.1353/ajm.2000.0021`.

## Strict scope: two incomparable dense chains below a third

Let

```text
P=(Q times {0}) disjoint_union (Q times {1}) disjoint_union (Q times {2}).
```

Order each copy of `Q` in the usual way, leave the first two copies
incomparable with one another, and declare

```text
(q,i) < (r,2)       for every q,r in Q and i in {0,1}.
```

There are no other comparisons.  Form the countable graph `E` with vertex
set `P` and, for every strict comparison `s<t` and every positive integer
`n`, an edge

```text
e_(t,s,n): t -> s.
```

The graph is acyclic, so `D=C*(E)` is AF.  Every vertex is an infinite
emitter.  Hereditary vertex sets are exactly the lower subsets of `P`,
saturation adds nothing because there are no regular vertices, and there
are no breaking vertices because a vertex emits either zero or infinitely
many edges to the complement of any hereditary set.  Condition (K) is
automatic.  Hence the ideal lattice of `D` is exactly the lower-set lattice
of `P`.

Put

```text
A_0=D tensor_min O_infinity.
```

The exact primitive-tensor-product theorem preserves the ideal lattice,
and `A_0` is separable, nuclear, and strongly purely infinite.

We verify the quotient-seed condition purely in the lower-set lattice.  Let
`H` be a proper lower subset of `P`.  If the zeroth rational copy is not
contained in `H`, then

```text
(Q times {0}) minus H
```

is a nonempty lower subset of the complementary quotient poset and is
totally ordered; its lower-set lattice is therefore a chain.  The same
argument uses the first copy if the zeroth is exhausted but the first is
not.  If both lower copies lie in `H`, properness leaves a nonempty tail in
the top copy indexed by `2`, again a totally ordered lower subset of the
quotient.
Thus every nonzero quotient of `A_0` contains a nonzero chain-ideal ideal.

On the other hand, no chain-ideal cover exists.  Every lower set containing
a vertex of the top copy must contain both entire bottom copies.  It then
contains two incomparable nonzero lower subsets and so its internal ideal
lattice is not a chain.  Consequently every chain-lattice ideal misses the
top copy, and the union of all such ideals is proper.

The example is also outside the other earlier regimes.  The rational
copies have no least element, so `P` has no minimal vertex and `A_0` has no
nonzero simple ideal.  Its primitive space has no isolated point and is not
scattered, and a continuous simple-layer series cannot even start.  Its
ideal lattice is infinite and non-chain.  Therefore the quotient-seed
theorem is strictly stronger than merely applying the finite, scattered,
simple-layer, global-chain, or chain-cover results already in the graph.

The tensor-space input is the existing Cairn import
`blanchard-kirchberg-exact-primitive-tensor-product`; the graph ideal
calculation is the same Condition-(K), no-breaking-vertex calculation
audited for `stw72-chain-ideal-cover-wpi-is-purely-infinite`.
