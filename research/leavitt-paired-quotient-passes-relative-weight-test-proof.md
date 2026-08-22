---
rg: 2
id: leavitt-paired-quotient-passes-relative-weight-test-proof
kind: route
title: Put unit weight on the two involution loops and prove the zero-weight labels are Nielsen reduced in the free product
target: leavitt-paired-quotient-passes-relative-weight-test
requires:
  - leavitt-paired-relative-picture-local-census
---

## The folded star graph

Write each relator starting at an occurrence of `z`:

```text
R_0 ~ z h_1 z h_2 z^(-1) h_0,
R_1 ~ z k_1 z k_2 z^(-1) k_0.
```

The relative star graph has vertices `z^+` and `z^-`.  With the convention
that a subword `z^epsilon g z^delta` gives an edge from `z^(-epsilon)` to
`z^delta` labelled `g`, its unoriented edges are

```text
label       endpoints
h_0         +,+
h_1         -,+
h_2         -,-
k_0         +,+
k_1         -,+
k_2         -,- .
```

Give the `h_2`- and `k_0`-edges weight one, in both orientations, and every
other edge weight zero.  Each relator has three star-graph edges and total
weight one, hence satisfies

```text
sum weights = 1 = 3-2.                              (WT1)
```

The weight-one edges are exactly the two torsion folds found by
`leavitt-paired-relative-picture-local-census`:

```text
h_2=e_0,       k_0=a_1,       h_2^2=k_0^2=1.
```

Their double traversals are admissible cycles of weight two, so this weight
choice is sharp.

The same census shows that no member of the symmetrized relator family is a
second full copy of another member: distinct cyclic conjugates overlap in at
most three of the six alternating syllables.  Thus the relative presentation
is orientable, as required in the original Bogley--Pride formulation of the
weight test.

## All zero-weight paths are Nielsen reduced

The four zero-weight labels have the following free-product normal forms:

```text
h_0=a_0 b_1,       h_1=c_0 d_1,
k_1=b_0 c_1,       k_2=d_0 e_1.                    (WT2)
```

Thus they are `u_(i,0)v_(i,1)` for

```text
(u_i)=(a,c,b,d),       (v_i)=(b,d,c,e).
```

The four `u_i` are pairwise distinct in `G_0`, and the four `v_i` are
pairwise distinct in `G_1`.  Indeed `a,b,c,e` are elementary roots with the
distinct nonzero Leavitt coefficients `s_0,s_1,t_0,t_1`, while `d=p` is the
twenty-cycle permutation matrix and is not one of those roots.  The standard
infinite-word representation also gives immediate separating basis vectors.

Consider a freely reduced word in the four symbols displayed in `(WT2)` and
their inverses.  At a positive-negative junction, the only possible
free-factor cancellation is `v_i v_j^(-1)`, which is the identity only when
`i=j`; that would be an excluded symbol-inverse pair.  At a
negative-positive junction the corresponding block is `u_i^(-1)u_j`, with
the same conclusion.  Positive-positive and negative-negative junctions
already alternate free factors.  Consequently every surviving junction
block is nonidentity, so the expanded word has a nonempty normal form in
`G_0*G_1`.

It follows in particular that:

1. no nonempty reduced zero-weight path has label one;
2. a nonempty closed zero-weight path has free-product length at least two,
   so its label is neither `h_2^(-1)=e_0` nor `k_0^(-1)=a_1`, each of which
   has free-product length one.

## The weight test

Let a reduced admissible cycle in the star graph have total weight less than
two.  If it uses no weight-one edge, item 1 gives a contradiction.  If it
uses exactly one, rotate the cycle to start with that loop.  The remaining
zero-weight path is closed at the same vertex, and admissibility would say
that its label is the inverse of `h_2` or `k_0`, contradicting item 2.
Therefore every reduced admissible cycle has weight at least two:

```text
weight(admissible cycle) >= 2.                       (WT2)
```

Conditions `(WT1)` and `(WT2)` are precisely the relative weight test.  The
weights are nonnegative, so this is the aspherical (not merely weakly
aspherical) form of the test.  Bogley--Pride, *Aspherical relative
presentations*, Proc. Edinburgh Math. Soc. **35** (1992), Section 2.2, then
gives diagrammatic reducibility.  Equivalently, assigning corner angles from
these weights makes every interior vertex have total angle at least `2 pi`
and every relator region have nonpositive curvature.  Relative asphericity
includes injectivity of the coefficient group, so the canonical map
`H -> Q` is injective.

Equivalently, naming the maximal folds

```text
y=z h_2 z^(-1),       v=z^(-1) k_0 z
```

turns the two half-relator overlaps into involution mirrors.  The zero-weight
Nielsen argument proves that no chain between those mirrors can close with
zero or one mirror.  Two mirrors have exactly the curvature cost needed by
the weight test; they do not create a coefficient-boundary diagram.
