---
rg: 2
id: finite-offset-relative-piece-pigeonhole-proof
kind: route
title: Repeat one port-equality label pair on an eight-syllable rectangle
target: finite-offset-pauli-rectangles-violate-relative-gr-sixth
requires:
  - pauli-rectangles-block-naive-relative-c-sixth
---

There are finitely many oriented pairs in

```text
P^(+-1) x (D_X union D_Z)^(+-1).
```

Every pair-port occurrence is adjacent inside its equality cloud to a
bounded positive number of equality edges.  Across an unbounded game family,
the pigeonhole principle gives two distinct immersed two-edge paths with the
same label.  In a graphical presentation this common path is a piece.

For the complete Pauli table, take the two logical pair tests at the ends of
the equality edge and complete them with the corresponding two tests in a
second row or column.  The resulting mixed rectangle alternates four pair
steps and four equality-factor steps.  Its relative length is at most eight
by `pauli-rectangles-block-naive-relative-c-sixth` and it contains the
repeated two-edge path.  The graphical `Gr'(1/6)` inequality is therefore
violated.

