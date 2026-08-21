---
rg: 2
id: relative-c-sixth-pauli-incidence-labeling
kind: claim
title: Give the occurrence Pauli family a free-product C-prime one-sixth labeling
distinct_from:
  balanced-pauli-incidence-labeling: that seeks an ordinary-word Greendlinger balance condition; this asks directly for the sharper free-product syllable condition in which equality clouds are coefficient factors.
  expander-cloud-reduction-preserves-pauli-dimension-gap: that proves arbitrary expander-cloud replacement preserves dimension; this must choose the replacements and pair ports to avoid all short or repeated relative mixed contours.
  equality-synchronized-lifts-create-two-pair-contours: that proves covering lifts and pair clouds synchronized by equality make the relative girth worse; this must use a non-equality synchronizing code or label the original threshold rectangles directly.
  finite-offset-pauli-rectangles-violate-relative-gr-sixth: that proves direct finite edge-type labeling of the complete rectangular core repeats a forbidden two-syllable piece; this must remove or absorb that core.
---

OPEN.  Starting from the same-Hilbert-space occurrence games supplied by
`expander-cloud-reduction-preserves-pauli-dimension-gap`, construct finitely
generated recursively presented equality groups `H_X,H_Z`, finite generator
sets `D_X,D_Z`, finite signed pair alphabets `P_0,P_1`, and a recursive
relative graphical presentation over

```text
F = H_X * H_Z * F(P_0 disjoint_union P_1)                      (RPC1)
```

such that:

1. every X or Z consistency edge is labeled in `D_X` or `D_Z`, and every
   signed pair edge is labeled in the corresponding `P_b`;
2. the occurrence graphs map to the relative Cayley graph with their
   equality clouds as the `H_X,H_Z` pieces;
3. every essential new mixed contour is cyclically reduced, has relative
   syllable length at least eight, and the symmetrized graphical relators
   satisfy free-product `Gr'(1/6)`;
4. the tested Pauli sign profiles separate logical X rows and Z columns;
5. all bounded local product/linearity decorations are valid in the exact
   coset-Clifford model and use only finitely many templates.

The eight-syllable lower bound is exact: a sign-double-coset collision has at
most four syllables, so Greendlinger rules it out.  A Pauli rectangle has at
most eight syllables, so every such rectangle must remain fully reduced and
cannot share an adjacent relative syllable pair with a second immersion.

## Attempts

- **Untyped Osajda labels.**  They control ordinary pieces but not pieces
  after an entire equality path is contracted to one coefficient syllable.
- **Independent equality expanders.**  They preserve soundness but can make
  two-pair bigons or repeated relative two-syllable patterns.
- **Arbitrary high-girth covers.**  They may fix the relative pieces but can
  unwind the dimension witness or lose it by an unbounded sheet factor.
- **High-girth pair clouds with equality synchronization.**  Their dimension
  decoder stays on the same Hilbert space, but any two copies of one logical
  pair edge close through the two equality fibers to a relative contour with
  at most four syllables.  This is the exact obstruction proved in
  `equality-synchronized-lifts-create-two-pair-contours`.
- **Directly color the threshold rectangles by finitely many port types.**
  The growing complete Pauli core has infinitely many pair/equality corners
  but only finitely many labels `p d`.  Two such corners repeat as a relative
  piece of length two on an eight-syllable relator, contradicting
  `Gr'(1/6)`.  This is proved in
  `finite-offset-pauli-rectangles-violate-relative-gr-sixth`.

The surviving combinatorial target cannot duplicate a logical pair edge
inside equality-connected endpoint fibers, and cannot color the growing
threshold core by only finitely many local types.  It must either absorb the
bounded rectangle templates into a sign-safe base group, replace the complete
table by a sparse robust dimension witness, or use a non-equality
synchronizing code whose logical decoder remains on the same Hilbert space.

The direct version is now ruled out by
`finite-offset-pauli-rectangles-violate-relative-gr-sixth`: finite edge
offsets repeat a two-syllable port/equality piece, while the complete table
places it on an eight-syllable rectangle.  Therefore this OPEN claim now
means a genuine **pre-replacement** of the mixed incidence geometry which
raises every such contour above relative length twelve while preserving the
same-Hilbert-space decoder.  Merely relabeling the original rectangles
cannot work.

Nor can one simply insert an unweighted sea of equality-only dummy vertices
to make the peripheral segment products unique.
`sparse-ports-either-lose-soundness-or-repeat-relative-pieces` gives the
dichotomy: vanishing port density loses the uniform Poincare decoder, while
positive port density forces a repeated bounded peripheral turn.  A sparse
replacement would need a genuinely new port-weighted agreement theorem.
