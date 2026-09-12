---
rg: 2
id: balanced-overlay-sparse-site-proof
kind: route
title: Corrupt two full-rank coordinates and count the balanced incident faces
target: balanced-overlay-sparse-sites-evade-hilbert-outlier-cut
requires: []
---

Each of coordinates `1,2` belongs to at most the fixed column-degree number
of original rows.  Hence only `O(1)` original row types and `O(M)` ordered
row pairs can see `(BSS1)`.  Repeating each original row `Theta(M)` times
therefore creates `O(M)` bad original-face copies, while the quadratic layer
has only `O(M)` bad pair-sum faces.  The balanced denominator is
`Theta(M^2)`, so these contributions are `O(1/M)=O(1/L)`.  The single bad
complete logical pair contributes only `O(1/L^2)`.

All matrices appearing in every bad residual are fixed words in `A,B`, so
their residual squares are bounded above by an absolute scalar multiple of
`I`.  At most an `O(1/L)` fraction of the balanced summands is nonzero.
Averaging these positive bounds gives `(BSS2)` in operator order.

Finally `||A-I||_op=||B-I||_op=2` when both signs occur, while their average
squared normalized-HS repair cost is at most `8/L`.  Thus the example
separates Hilbert-sector truncation from sparse-site repair exactly as
claimed.
