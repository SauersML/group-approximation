---
rg: 2
id: haar-algebraic-koopman-proof
kind: route
title: Fourier-dualize the action and count fixed-subgroup cosets
target: haar-algebraic-actions-have-permutation-koopman-spectrum
requires: []
---

The characters `chi_a`, `a in K-hat`, form an orthonormal basis of
`L^2(K)`, and an automorphism sends `chi_a` to `chi_(g.a)`.  Thus Koopman is
the permutation representation on `ell^2(K-hat)`.  Equivariant pullback
embeds the Koopman representation of every measurable action factor into
this permutation representation.

For finite `F` in the acting group, `Fix_K(F)` is a closed subgroup.
Distinct cosets have equal Haar mass, so finite index `n` gives mass `1/n`,
while infinitely many disjoint equal-mass cosets force mass zero.  In a
linear `F_p` subshift every finite index is `p^r`, giving the stated cylinder
law.  These arguments prove both asserted obstructions.
