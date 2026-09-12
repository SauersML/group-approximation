---
rg: 2
id: agent-free-compressor-minimal-nonretractive-corner
kind: claim
title: Three corner rows are the minimal nonretractive free-compressor coupling
distinct_from:
  shared-bcs-carrier-localizes-free-compressor-quotient: That asks for these algebraic corner identities to be recovered with dimension-uniform control from arbitrary normalized-HS group microstates; this proves the exact coefficient-module theorem and isolates the three indispensable rows.
  agent-free-compressor-hnn-letter-preserves-product-split: That retains the HNN and payload corner but does not identify the free action with a nonstationary finite packet type; this adds precisely that missing identification.
  predicate-rank-jump-forces-adjoint-reynolds-gap: That computes the finite packet rank gap once parent and child act on one carrier; this proves that the three corner rows put those two actions on one carrier.
---

Let `A<B` be the fixed predicate packet inclusion, over a splitting field
whose characteristic is coprime to `|B|`.  Choose generators
`b_1,...,b_m` of `B`, words `a_i` generating `A`, a free group
`F=<x_1,...,x_m>`, and an injective endomorphism `alpha` with

```text
theta(x_i)=b_i,                 theta(alpha(x_i))=a_i. (MNC1)
```

Let `P` be a central packet idempotent on whose isotypic types the Reynolds
rank difference

```text
rank(P e_A)-rank(P e_B)>=gamma rank(P)                 (MNC2)
```

holds for a fixed `gamma>0`.  In the coefficient presentation impose exactly
the following three kinds of corner rows:

```text
[P,u_(x_i)]=0,  P(u_(x_i)-b_i)=0         (1<=i<=m),    (MNC3)
[P,t]=0,                                                (MNC4)
t u_(x_i) t^(-1)=u_(alpha(x_i))          (1<=i<=m).    (MNC5)
```

Then every finite-dimensional coefficient-module representation has

```text
P=0.                                                     (MNC6)
```

Indeed `(MNC3)` places the named parent `B` action on `PH`, `(MNC4)` keeps the
stable letter on that same carrier, and `(MNC5)` conjugates its `B`-fixed
space onto its `A`-fixed space.  Their ranks must be equal, contradicting
`(MNC2)` unless `PH=0`.

These rows are nonretractive in exactly the required sense.  In a product
model with the payload in one factor and the mapping torus in another,
`(MNC3)` forces the first-factor free action to equal the prescribed packet
action.  Then `(MNC4)--(MNC5)` force the nonstationary `B/A` comparison in
that same factor, where `(MNC2)` rules it out.  Thus the product models of
`agent-free-compressor-hnn-letter-preserves-product-split` cannot extend over
`(MNC3)` on a nonzero selected packet type.

The coupling has exact perfect completeness.  In the perfect tracial BCS
model the forbidden idempotent is `P=0`, so `(MNC3)--(MNC4)` are vacuous;
the ordinary free mapping-torus representation satisfies `(MNC5)` and keeps
the marked word nontrivial.

The three ingredients are individually necessary for this rank argument:

1. without `(MNC3)`, the payload and mapping torus split as in
   `agent-free-compressor-hnn-letter-preserves-product-split`;
2. without `(MNC4)`, the stable letter may transport `P` to a disjoint
   compensation carrier, so no same-corner rank equality follows;
3. without `(MNC5)`, the parent and child packet actions are not compared.

Accordingly, the remaining analytic theorem is not to discover another
algebraic relation.  It is to authenticate `(MNC3)--(MNC5)` on the physical
payload carrier of an arbitrary normalized-HS representation of their
ordinary rank-five wordization.  The product-ring no-go proves that
authenticating only `(MNC4)--(MNC5)` cannot suffice.
