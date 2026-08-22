---
rg: 2
id: spaas-chordal-stability-does-not-cross-the-ldpc-quotient-gate
kind: claim
title: Spaas's chordal stability does not cross the repeated-LDPC quotient and uniform-family gates
distinct_from:
  chordal-abelian-graph-products-hs-stable: that imports strict HS stability for each fixed chordal graph product; this checks the growing repeated-LDPC occurrence presentation against the exact graph-product hypotheses and uniformity of the proof.
  quadratic-repetition-supports-complete-commutation-overlay: that gives a bounded-occurrence exact encoding of all logical commutations; this explains why its equality and parity relations lie outside the graph-product theorem.
  sparse-clifford-cycles-refute-average-commutator-rounding: that gives the quantitative average-commutator counterexample; this uses it to separate fixed-group HS stability from the growing average-relator modulus needed by the compiler.
---

Primary-source audit: Pieter Spaas, *Hilbert--Schmidt stability for graph
products*, arXiv:2603.02058v1 (2 March 2026), Definitions 1, 5, and 6,
Theorems 8 and 9, and Corollary 10.

Spaas proves **strict same-dimension** HS stability.  For a fixed group
`Gamma`, Definition 1 corrects maps `phi_n:Gamma->U(k_n)` by homomorphisms
`psi_n:Gamma->U(k_n)` in the same matrix dimensions.  Corollary 10 applies
this to a graph product of countable abelian vertex groups over one fixed
finite chordal graph.  The C-star proof likewise lifts into the same matrix
algebras `M_i`; there is no flexible amplification in the conclusion.

The theorem does not apply to the bounded-occurrence repeated-LDPC
presentation.  A graph product has only

```text
internal relations inside each vertex group,
[Gamma_v,Gamma_w]=1 for graph edges (v,w).               (SCL1)
```

The occurrence presentation additionally has two different kinds of
relations:

```text
Q_(i,j)=Q_(i,j')               (copy equality),
product_(i in check c) Q_(i,j(c,i))=1.                  (SCL2)
```

Relations `(SCL2)` identify or quotient elements belonging to different
occurrence vertices.  They are neither vertex-group relations on disjoint
free factors nor edge commutators.  Thus the occurrence group is a quotient
of an appropriate graph product, not the graph product covered by Theorem 8.
HS stability does not pass to arbitrary quotients, so this reformulation
does not transfer the theorem.  Concretely, free groups are HS-stable while
every finitely generated group is their quotient, and Spaas's Remark 12 cites
Ioana's non-HS-stability of `F_2 x F_2`; quotient permanence is therefore
false even among finitely presented groups.

There is an exact two-sided structural fence.

1. **Collapse copies and parities first.**  The same-basis exact group becomes
   the abelian scalar code group (a quotient of `C_2^L`), hence can be written
   as a complete-graph product and is HS-stable for every fixed `L`.  But the
   complete graph gives each logical coordinate `Theta(L)` commutation
   incidences and discards the bounded-occurrence presentation whose average
   loss is the object to be rounded.
2. **Keep the bounded-degree occurrences.**  The commutation edges themselves
   can be made chordal (indeed the pair overlay is a matching), but then the
   equality and parity relations `(SCL2)` remain external quotient/amalgam
   data.  Spaas's inductive step adds a vertex commuting with a clique; it
   does not glue two vertex algebras by identifying a shared coordinate or
   impose a parity word across them.  Cyclic Tanner overlaps therefore cannot
   be treated as an iterated chordal graph product by that proof.

Nor does the paper provide the needed uniform growing-family modulus.  Its
statement is asymptotic for one fixed graph product.  The proof is an
ultraproduct lifting argument, inducts on the number of graph vertices, and
uses graph-dependent finite partitions of the neighboring commutative
algebras.  It states no `delta(epsilon)` uniform in the graph, its number of
vertices, or a varying presentation.

This lack of uniformity is load-bearing rather than cosmetic.  The complete
graph products `C_2^L` are individually strict HS-stable, while
`sparse-clifford-cycles-refute-average-commutator-rounding` gives `L`
reflections with average complete-pair commutator energy `8/L -> 0` but
average squared distance at least `1/4` from every commuting tuple.  Hence
fixed-graph stability cannot be diagonalized into the uniform
average-relator theorem required as `L->infinity`.  Spaas's definition tests
each fixed group element along a sequence for one group; it does not turn a
vanishing fraction of bad relations in a moving complete graph into a
nearby representation.

The sparse Clifford example does not settle the repeated-LDPC system because
its parity checks may exclude that tuple.  It proves the sharp boundary:
Spaas can be used after the occurrence system has already been rounded to one
fixed chordal graph-product representation, but it supplies neither the
joint parity-plus-commutation estimate nor the quotient/amalgam preservation
theorem needed to perform that rounding.

With the current Cairn sharpening, that joint estimate is exactly
`operator-unique-neighbor-cosystolic-rounding`: an operator-valued LTC or
cosystolic inequality plus a kernel-killing bootstrap.  Spaas's theorem
contains neither input because the parity two-cells are absent from `(SCL1)`.
