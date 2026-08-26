---
rg: 2
id: leavitt-preimage-whitehead-moving-bridge
kind: route
title: Pull the literal moving Whitehead back through the Leavitt compression cell
target: el20-six-moving-coefficient-square-bridges
requires:
  - leavitt-whitehead-20x20-compression-cell
  - literal-whiteheads-give-gauged-moving-bridge-table
---

**INVALIDATED PREIMAGE-WHITEHEAD ROUTE.**  The smallest nonnormal
full-Leavitt candidate is the three-root partial Whitehead with coefficients
`s_0,t_0`.  Rootwise Leavitt compression sends it exactly to the first
literal moving Whitehead; one further compression sends the corresponding
depth-one word to the second literal Whitehead.  Thus a conjugate by the
20-by-20 Hilbert-hotel word has the right full Gram.

`compression-preimage-whitehead-preserves-gauge` proves that this exact
rewrite only transports the selector gauge to the preimage cut.  It does
not cancel it.  The bounded occurrence table has exact finite-dimensional
amplifications with a nontrivial involution on both Whiteheads, so the
compression identity alone cannot give `(ESB2)`.

