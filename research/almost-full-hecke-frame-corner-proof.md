---
rg: 2
id: almost-full-hecke-frame-corner-proof
kind: route
title: Fill the missing Hecke-frame trace and bound the error column
target: almost-full-hecke-frame-gives-flexible-corner
requires:
  - hecke-top-spectrum-coverage-controls-window
---

Add \(A_0=(1-\sum_{j\geq1}A_j^*A_j)^{1/2}\).  The resulting Kraus
column is unital.  Near-top spectral calculus bounds the squared
intertwining error of the original columns by \(2\epsilon\); the filler
has squared error at most \(4\tau(1-P)\leq4\delta\).  Multiplication of
the combined error column by the coisometric Kraus row gives the marked
coefficient error, hence the bound \(\sqrt{2\epsilon+4\delta}\).
