---
rg: 2
id: relative-c-sixth-pauli-incidence-labeling
kind: claim
title: Give the occurrence Pauli family a free-product C-prime one-sixth labeling
distinct_from:
  balanced-pauli-incidence-labeling: that seeks an ordinary-word Greendlinger balance condition; this asks directly for the sharper free-product syllable condition in which equality clouds are coefficient factors.
  expander-cloud-reduction-preserves-pauli-dimension-gap: that proves arbitrary expander-cloud replacement preserves dimension; this must choose the replacements and pair ports to avoid all short or repeated relative mixed contours.
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

The surviving combinatorial target is a replacement-product labeling whose
cloud decoder stays on the same Hilbert space and whose pair-port rotation
system makes every relative rectangle unique.

