---
rg: 2
id: functional-support-is-affine-exactly-on-an-affine-domain-map
kind: claim
title: A functional accepted support is affine exactly when its active domain and map are affine
distinct_from:
  tailored-gap-is-lcs-or-has-a-nonaffine-edge: that gives the general all-affine-edge dichotomy for a fixed tailored game; this classifies the tempting projection/functional special case and isolates its hidden domain obstruction.
  hadamard-pcpp-reflects-affine-unsafety: that propagates an existing odd-xor violation through answer reduction; this decides when a functional source support has such a violation in the first place.
  taller-vidick-lcs-re-hardness: that records an imperfectly complete projection-game output; this explains why the word projection does not itself supply the affine-safe perfect support needed here.
---

**ESTABLISHED FUNCTIONAL-SUPPORT CLASSIFICATION.**  Fix binary encodings of
two finite answer alphabets and let a positive accepted-pair support be the
graph

```text
E={(a,f(a)):a in D} subseteq F_2^r times F_2^s.          (FSA1)
```

Then `E` is an affine subset of the ambient Boolean answer space if and only
if

```text
D is affine, and f:D->F_2^s is an affine map.            (FSA2)
```

More generally, for an arbitrary positive sub-support `D_0 subseteq D`, its
graph is affine-safe inside the full functional acceptance relation exactly
when every odd affine combination of points of `D_0` stays in `D` and `f`
respects that combination.  Thus functionality or uniqueness by itself says
nothing about affine safety once three or more active labels are present.

There is one sharp small-alphabet exception.  A total binary projection
constraint has `D=F_2` and a function `f:F_2->F_2`; every such function is
affine.  Hence every two-answer projection-game edge is an affine relation.
A finite game all of whose constraints have this form is already a binary
LCS after writing each graph as affine parity equations.  Therefore a
published perfect-commuting-versus-finite-dimensional-gap family of binary
projection games would not be a preprocessing trick: it would already close
the non-hyperlinear solution-group endpoint.

The known smooth-label-cover constructions do not meet this exception.
Their projection maps can be coordinate restrictions, but their active
labels are tuples of satisfying clause assignments.  Those domains are
products of seven-point 3SAT relations, not affine Boolean cubes.  Restricting
an affine coordinate map to a nonaffine domain leaves the graph nonaffine by
`(FSA2)`.  Padding to a full Boolean label cube without separately rejecting
the added labels creates new exact answers and loses soundness; rejecting
them reinstates precisely the nonlinear local predicate one was trying to
remove.

Consequently, searching for a projection or functional verifier is not a
bypass of the CMPS support gate.  A viable source must additionally certify
that the **positive active label domain** in one perfect HALT model is affine
and that every projection is affine on it.  If this holds on every edge, the
source is already an LCS gap; if it fails, the same odd-xor obstruction
returns before the Hadamard-PCPP layer.

