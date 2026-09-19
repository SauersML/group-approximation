---
rg: 2
id: sparse-parabolic-atom-has-split-inertia
kind: claim
title: A sparse parabolic character atom has split scalar inertia and no fixed rank holonomy
artifacts:
  - research/sparse-parabolic-split-inertia-proof.md
distinct_from:
  surviving-leavitt-corona-character-has-infinite-parabolic-orbit: that proves the full orbit of every nontrivial character is infinite; this computes the inertia group and shows that the infinite orbit supplies no projective holonomy on its rank-one atoms.
  binary-leavitt-finite-actor-minimal-atom-dichotomy: that gives a finite crossed-product countermodel for an arbitrary finite invariant root packet; this treats the literal split parabolic and shows directly why every loop based at one global character has scalar, cohomologically trivial holonomy.
  maximal-sparse-character-atom-does-not-return-multiplicity: that rules out comparing a returned global sector with coordinatewise maximal exact atoms; this rules out extracting a fixed noncommutative rank certificate from the parabolic orbit groupoid itself.
---

**ESTABLISHED SPLIT-INERTIA FENCE.**  Let `N` be an elementary abelian
`2`-group, let `H` act on `N`, and put

```text
G=N semidirect H.
```

For `chi:N->{+1,-1}`, let

```text
H_chi={h in H:chi(hnh^(-1))=chi(n) for every n in N},
I_chi=N semidirect H_chi.                              (SPI1)
```

Then `chi` extends to a one-dimensional representation of its full inertia
group:

```text
chi_tilde(nh)=chi(n),                 n in N, h in H_chi. (SPI2)
```

Consequently the character-orbit representation induced from `chi_tilde`
has rank-one `N`-character atoms, and every parabolic word returning the
`chi` atom acts there by a scalar.  The loop holonomy is split: commutators
of returning words act as `+1`, and tensoring by an arbitrary representation
of `H_chi` installs an arbitrary ordinary multiplicity gauge without changing
the orbit table.  Thus parabolic covariance and any fixed collection of
same-atom parabolic returns do not force a Pauli pair, a rank increase, or a
properly infinite corner.

There is no hidden branching inequality among different orbit atoms either.
Every actor permutes characters bijectively.  In the induced model it maps
one rank-one atom unitarily onto one rank-one atom.  If several labelled paths
enter the same character, their ranges are the same line and their
cross-Grams have full modulus; they are not orthogonal copies to which a
Bessel/rank overflow argument applies.

Apply this to the literal maximal parabolic

```text
N=<x_(i n)(a):1<=i<n,a in L>,
H=St_(n-1)(L),                 L=L_(F_2)(1,2).         (SPI3)
```

The orbit of a nontrivial sparse corona character is infinite by
`surviving-leavitt-corona-character-has-infinite-parabolic-orbit`, but this
does not alter `(SPI2)`.  More concretely, the one upper-left root subgroup
used to prove infinitude is additively isomorphic to `(L,+)`.  Every fixed
finite list of its coefficients generates a finite elementary abelian
subgroup.  Its orbit of `chi` is therefore a finite set with an exact finite
permutation--diagonal model whose character atoms all have rank one.  Every
loop in that finite orbit has the split scalar holonomy above.

Hence no fixed finite ordinary-word certificate obtained solely from the
infinite single-root parabolic orbit, its character covariance, and its
same-atom return loops can contradict finite matrix rank.  A successful
sparse-atom proof must use at least one occurrence outside this split
normalizer geometry--for example a genuinely opposite-root word which no
longer permutes the abelian character atoms--or must provide a bounded-cost
fold of an unbounded orbit back into the same multiplicity reservoir.  The
mere infinitude of the orbit supplies neither.

No Property `(T)`, trace-density assumption, canonical character, stability
theorem, computation, or literature input is used.

DERIVATION
sparse-parabolic-split-inertia-proof
