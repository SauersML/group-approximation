---
rg: 2
id: finite-offset-pauli-rectangles-violate-relative-gr-sixth
kind: claim
title: Finite-offset Pauli rectangles violate direct relative Gr-prime one-sixth
distinct_from:
  relative-c-sixth-protects-sign-double-cosets: that theorem is correct once its relative small-cancellation hypotheses hold; this proves that the unmodified complete Pauli occurrence family cannot satisfy them.
  pauli-rectangles-block-naive-relative-c-sixth: that counts the threshold eight syllables; this adds the finite-offset pigeonhole which produces a forbidden two-syllable graphical piece.
---

Consider infinitely many occurrence-cloud reductions of complete finite
Pauli commutation tables.  Assume:

1. pair-port edges use one finite label set `P`;
2. equality-cloud edges use one finite label set `D_X union D_Z`;
3. every equality edge joins two occurrences which participate in pair tests,
   and the complete table supplies a Pauli rectangle through that edge.

After contracting maximal equality paths to coefficient-factor syllables,
the resulting family cannot be a graphical free-product `Gr'(1/6)` family.

Indeed, finite labels and infinitely many port/equality incidences force one
oriented two-edge label pattern `p d` (or `d p`) to occur at two essentially
distinct locations.  It is therefore a graphical piece of relative length
two.  By clause 3 each occurrence lies on an essential Pauli rectangle, whose
relative contour has length at most eight.  But `Gr'(1/6)` would require

```text
2 < 8/6,
```

which is false.

Thus direct threshold relative small cancellation is unavailable.  A live
construction must first replace the incidence geometry so that mixed
contours are longer than twelve relative syllables, or use the ordinary-word
balanced Greendlinger route where equality arcs contribute their full
length.

