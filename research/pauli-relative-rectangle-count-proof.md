---
rg: 2
id: pauli-relative-rectangle-count-proof
kind: route
title: Alternate four pair letters with four equality-factor syllables
target: pauli-rectangles-block-naive-relative-c-sixth
requires: []
---

Traverse a four-cycle alternating X and Z logical clouds.  Each X--Z step is
one pair-letter syllable.  Between consecutive pair-edge occurrences at a Z
logical observable, the equality-cloud path is one element of `H_Z`, hence
at most one relative syllable; the analogous X path is one element of
`H_X`.  Four pair steps and four equality paths give `(PR8-1)`.  Free
reduction can only shorten the contour.

Occurrence splitting and expander-cloud consistency change the ordinary
lengths of the equality paths, but not their free-product syllable lengths:
an arbitrarily long word entirely in `H_X` or `H_Z` is still one syllable.
Therefore the obstruction survives the dimension-preserving expander-cloud
degree reduction.

