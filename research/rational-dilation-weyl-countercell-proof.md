---
rg: 2
id: rational-dilation-weyl-countercell-proof
kind: route
title: Reduce the rational dilation torus and its truncated Weyl module modulo one untouched prime
target: finitely-generated-rational-dilations-preserve-char-p-weyl-cells
requires:
  - char-p-weyl-blocks-local-commutator-decoder
---

Reduce the finitely generated subgroup `Lambda<Q^x` modulo a prime avoiding
the finitely many prime divisors in its generators.  On
`F_p[t]/(t^p)`, multiplication `M` and differentiation `D` obey
`DM-MD=I`.  The diagonal maps `H_a(t^j)=a^j t^j` form an exact
multiplicative representation of `F_p^x` and conjugate `M,D` by the weights
`a,a^(-1)`.

Use these inner coefficient automorphisms to form the finite semidirect
product `E_3(M_p(F_p)) semidirect bar(Lambda)`.  The paired Steinberg word is
`e_13(I)`, all dilation covariance holds exactly, and the left regular
representation supplies the canonical finite trace.  Since a complex
additive commutator cannot approach `I` within normalized-HS distance below
one, the rational dilation extension retains the bare Weyl countercell.
