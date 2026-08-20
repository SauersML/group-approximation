---
rg: 2
id: adjoint-supertrace-cannot-pay-hs-selection-load-proof
kind: route
title: Compare one operator-space direction with a balanced carrier cut
target: adjoint-supertrace-cannot-pay-hs-selection-load
requires: []
---

Take even `d` and let `x` be diagonal with `d/2` entries `1` and `d/2`
entries `-1`.  Then `tau_d(x)=0` and `||x||_2=1`.  The span `E=Cx` has
normalized adjoint projection rank `1/d^2`, while the positive spectral cut of
`x` has matrix trace `1/2`.  Likewise `span{I}` has adjoint rank `1/d^2` while
the support of its nonzero vector has trace one.  These ratios diverge with
`d`, proving that no dimension-free comparison exists.

