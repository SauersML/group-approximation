---
rg: 2
id: bounded-neighbor-pauli-needs-growing-equality-components
kind: claim
title: Bounded-neighbor Pauli tests need growing equality components
distinct_from:
  pauli-braiding-test-exponential-dimension: that supplies a genuine unbounded dimension witness using linearity and consistency; this proves that sparse pairwise Pauli signs alone can never be such a witness.
  two-transitive-occurrence-sections-have-unbounded-pair-holonomy: that obstructs global sections for a dense pair orbit; this is an exact constant-dimensional countermodel before any section is chosen.
---

Let `G=(V,E_0 sqcup E_1)` be a finite simple graph of maximum degree at
most `Delta`, with an edge in `E_b` asking for two reflection observables to
commute when `b=0` and anticommute when `b=1`.  There is an exact Pauli
realization of every such test in a dimension depending only on `Delta`, not
on `|V|`.  One may take

```text
C = Delta^2+1,      m = binom(C,2),      dim <= 2^m.             (BNP1)
```

Consequently no family consisting only of bounded-degree involution and
pairwise commute/anticommute tests can have a dimension lower bound tending
to infinity.

More generally, allow equality edges between occurrence copies and contract
their connected components.  If every equality component has at most `M`
vertices, the original test graph has degree at most `Delta`, and the
contracted signed constraints are consistent (no anticommuting loop or
parallel pair carrying both signs), then all equality and signed-commutator
tests have one exact realization in dimension bounded in terms of
`M,Delta` alone.  Therefore any perfect-complete bounded-neighbor Pauli
occurrence compiler with an unbounded dimension witness must use at least one
of the following genuinely global mechanisms:

1. equality/linearity components whose sizes tend to infinity;
2. bounded-arity tests not reducible to equality plus pairwise Pauli signs;
3. additional address-covariance constraints which themselves carry the
   dimension obstruction.

This makes expander consistency load-bearing rather than cosmetic.  Sparse
Pauli anticommutation on a Cayley graph is not an error-spread mechanism by
itself.

The matrix-completion form of the same phenomenon is
`bounded-degree-partial-matrices-have-constant-completion-rank`, with the
explicit bound `Delta+ceil(log_2 Delta)+1`.  Additive generator-column tests
can evade it because repeated occurrences must receive labels from one common
linear map; `degree-one-generator-columns-have-sqrt-minrank-but-no-gap`
exhibits degree-one exact minrank `Theta(sqrt(n))`.  Its vanishing robust gap
confirms that the distinction is real but does not yet supply the desired
dimension witness.
