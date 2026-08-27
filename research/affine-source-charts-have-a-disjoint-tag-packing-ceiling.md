---
rg: 2
id: affine-source-charts-have-a-disjoint-tag-packing-ceiling
kind: claim
title: A rank-r affine source atom supports at most two-to-the-r disjoint full-mass tag copies
distinct_from:
  affine-auxiliary-control-flow-barrier: that says affine group words cannot compute a nonlinear predicate; this counts how many repeated copies of one already selected affine atom can be separated by conjugating enlarged abelian tag charts.
  finite-group-selector-induction-barrier: that gives the regular-representation obstruction to deleting unwanted selector sectors; this is the exact character-space packing bound after adding arbitrary unconstrained dummy tag bits.
  constant-repetition-v4-needs-only-disjoint-tags: that permits any pairwise-disjoint finite tag types; this fences the simplest construction of those types by affine HNN charts.
---

Let `D=C_2^r`, let `E=C_2^t`, and put `H=D times E`.  In a representation
whose `E`-type is regular over the `D`-character atom `chi`, the full source
atom has character support

```text
S_chi={chi} times E^hat,                |S_chi|=2^t.    (ASP1)
```

Conjugating the source chart to a common target chart by any automorphism of
`H` sends `(ASP1)` to an affine `t`-plane in `H^hat`.  If `L` repeated copies
of the whole source atom are assigned pairwise disjoint target tag sets, then

```text
L 2^t <= |H^hat|=2^(r+t),
L <=2^r.                                               (ASP2)
```

The same conclusion holds asymptotically in canonical microstates, because
the restriction to the fixed finite dummy subgroup `E` converges to regular
type and discarding a nonzero fraction of its characters discards the same
fraction of source mass.

Thus adding arbitrarily many unconstrained commuting tag bits does not make
constant repetition free: the extra bits enlarge each source atom and the
target character space by the same factor.  For the repeated V4 programme,
plain selector/radical HNN conjugacies can separate at most `2^r` copies of
one fixed selector-radical atom, where `r` is the number of already fixed
affine bits.  If the repetition count required by `(CRV4)` exceeds this
number, the tagger must use nonabelian representation type, shared-context
operator data, or an actual amplification mechanism; dummy affine clocks do
not suffice.

The same proof works verbatim over every prime alphabet.  For
`D=C_p^r`, `E=C_p^t`, a full source fiber has `p^t` characters inside a
target dual of size `p^(r+t)`, so pairwise disjoint affine images satisfy

```text
L p^t <= p^(r+t),                 L<=p^r.               (ASP3)
```

In particular, using the order-`p` phase protected by the
Slofstra--Zhang high-girth theorem as a larger fixed character alphabet does
not create Plancherel surplus.  The `p` possible cyclic characters each have
regular trace `1/p`; injective power maps only permute them.  Odd-order phase
survival may protect a mark, but it does not evade the fixed-atlas packing
ceiling.
