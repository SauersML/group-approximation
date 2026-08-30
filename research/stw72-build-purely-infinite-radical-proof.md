---
rg: 2
id: stw72-build-purely-infinite-radical-proof
kind: route
title: Close purely infinite ideals under finite sums and then take their directed union
target: stw72-purely-infinite-radical-reduction
requires: []
artifacts:
  - research/artifacts/stw72-purely-infinite-radical-audit-2026-08-30.md
---

Let `S` be the family of purely infinite closed ideals of `A`.  If `I,J` are
in `S`, then `I+J` is closed and

```text
0 -> I -> I+J -> J/(I intersect J) -> 0
```

is exact.  The quotient on the right is purely infinite.  Quotient and
extension permanence of Kirchberg--Rordam pure infiniteness therefore make
`I+J` purely infinite.  Induction gives the same conclusion for every
finite sum of members of `S`.

The finite subsets `F` of `S`, ordered by inclusion, form a directed set.
Write

```text
D_F=sum_(I in F) I.
```

The connecting maps are injective inclusions and their C-star inductive
limit is

```text
closure(union_F D_F)=closure(sum_(I in S) I)=P_pi(A).
```

Pure infiniteness is preserved by arbitrary directed C-star inductive
limits, so `P_pi(A)` is purely infinite.  It contains every purely infinite
ideal by construction and hence is the unique largest one.

Now suppose `A` is weakly purely infinite and put `P=P_pi(A)`, `B=A/P`.
Weak pure infiniteness passes to quotients, so `B` is weakly purely
infinite.  If `K` were a purely infinite ideal of `B`, its inverse image
`J` in `A` would fit into

```text
0 -> P -> J -> K -> 0.
```

Both end terms are purely infinite, so extension permanence would make `J`
purely infinite.  Maximality of `P` would give `J subset P`, and hence
`K=0`.  Thus `B` has no nonzero purely infinite ideal.

Every ideal of a weakly purely infinite algebra is weakly purely infinite.
Kirchberg--Rordam's characterization therefore says, for every ideal `I` of
`A`,

```text
I is purely infinite  iff  I has the Global Glimm Property.
```

Thus the ideals occurring in the definition of `P` are exactly the Global
Glimm ideals, and `P` is the unique largest such ideal.  The same argument
inside `B` shows that no nonzero ideal of `B` has the Global Glimm Property.
Weakly purely infinite algebras are nowhere scattered.  Hence
Thiel--Vilalta's Cuntz-semigroup characterization of the Global Glimm
Property implies that `Cu(L)` fails ideal-filteredness or property (V) for
every nonzero ideal `L` of `B`.

If `P=A`, then `A=P` is purely infinite.  Conversely, if `A` is purely
infinite, then `A` itself occurs in the defining family and `P=A`.  This
proves the first equivalence.  If `A` is not purely infinite, then `B` is
nonzero.  Every nonzero ideal `L` of `B` is weakly purely infinite because
weak pure infiniteness passes to ideals, but `L` cannot be purely infinite
because `B` has no nonzero purely infinite ideal.  This proves the
hereditary-counterexample assertion.

Finally, suppose the weak-to-plain implication were known for every weakly
purely infinite algebra with zero purely infinite radical.  Apply it to
`B`.  It would make `B` purely infinite; since `B` has no nonzero purely
infinite ideal, this forces `B=0`, and then `A=P` is purely infinite.  The
reverse reduction is immediate.  Quotients preserve nuclearity,
separability, and exactness, giving the stated category preservation.
