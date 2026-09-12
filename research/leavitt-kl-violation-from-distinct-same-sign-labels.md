---
rg: 2
id: leavitt-kl-violation-from-distinct-same-sign-labels
kind: route
title: Dead - look for a Leavitt violation among words with four coincidence-free same-sign corners
target: kl-violating-equation-over-leavitt-unit-group
requires: []
---

**Dead.** Invalidated by `kl-four-same-sign-corner-words-inject`.

After splitting powers of `t`, a nonsingular word with at least four
same-sign corners that close no trivial star-graph 2-cycle is aspherical over
every coefficient group. So it injects `R^x` and cannot violate. This holds
whatever the other same-sign labels do.

Consequences for the search:

- The rule covers the length-six classes `+++++-` and `++++--` whenever their
  four same-sign labels do not coincide.
- It needs no finite-order hypothesis on the sign-change coefficients.
- It includes the full-support torsion candidate `(L6.1)`.

A surviving candidate has at most three light same-sign corners. Every other
same-sign corner must repeat a label of its own type or invert a label of the
other type.

Recorded so that the census does not revisit these words.
