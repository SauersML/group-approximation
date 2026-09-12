---
rg: 2
id: chordless-paths-prove-noncentral-norm-feedback-rigidity
kind: route
title: Detect a corner kernel or move a derivative defect beyond the inverse's finite determining set
target: noncentral-norm-feedback-surjunctivity-iff-corner-finiteness
requires: []
artifacts:
  - research/artifacts/gottschalk-noncentral-norm-feedback-rigidity-and-corner-equivalence-2026-09-08.md
---

The parity-majority involution transforms norm feedback to

    P(d,m)=(d+Km,N(d)+Bm),
    K=(1-E)aE,       B=e+eae,

on even triples d and invariant triples m. The function N is zero
on the zero even triple and one on the other three. Its derivative
in any nonzero even direction takes both bit values. A nonzero
h in ker B therefore supplies an immediate collision of P, proving
B injective whenever F_a is injective.

When B is bijective, normalize w=Bm and set L=KB^-1. Draw an edge
j -> i between right-t orbits when the corresponding coefficient
of L is nonzero. A shortest directed cycle has no extra internal
edges, so its indicator h satisfies supp(h) contained in supp(Lh).
The blockwise derivative of N then constructs a collision.

If this transitive finite-propagation graph is acyclic but has an
edge, a fixed vertex has infinitely many ancestors. Choose an
ancestor outside the finite determining set of the inverse and a
shortest path to the fixed vertex. The path has no internal chords.
For its indicator h, every active row except the first has exactly
one nonzero incoming contribution. The derivative equation can be
met everywhere except that first block. The resulting two outputs
differ only there, while their inputs differ at the fixed endpoint.
This contradicts the inverse's finite determining set.

Thus L=K=0. Corner direct finiteness makes the already injective B
bijective, completing sufficiency. The corner norm subclass gives
necessity by the explicit conjugacy to B and identity coordinates.
