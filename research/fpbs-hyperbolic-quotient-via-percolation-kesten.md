---
rg: 2
id: fpbs-hyperbolic-quotient-via-percolation-kesten
kind: route
title: Hyperbolic quotients via the percolation Kesten gap along the kernel
target: fpbs-hyperbolic-quotient-every-generating-set
requires:
  - fpbs-percolation-kesten-normal-gap
  - fpbs-relative-gap-along-any-subgroup-separates
---

Let `H` be infinite and normal in `Gamma`, with `Gamma/H` non-elementary
hyperbolic. A non-elementary hyperbolic group contains `F_2`, so it is
nonamenable. `fpbs-percolation-kesten-normal-gap` with `N = H` gives
`p_c(G) < p_c(H;G)`, and `fpbs-relative-gap-along-any-subgroup-separates` then
gives `p_c < p_u`. ∎

This route uses no geometry of the quotient beyond nonamenability. So the
hyperbolic-quotient problem is no harder than the percolation Kesten gap for
its kernel.
