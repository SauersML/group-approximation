---
rg: 2
id: algebraic-compact-action-group-factor-compiler-proof
kind: route
title: Fourier-transform the algebraic action and use hereditary Connes embeddability
target: algebraic-compact-action-group-factor-compiler
requires: []
artifacts:
  - research/artifacts/nonhyperlinear-breakout-portfolio-2026-08-21.md
---

Fourier transform identifies `L^infinity(K)` with the group von Neumann
algebra `L(A)` by sending each character of `K` to the corresponding canonical
group unitary.  Because the action on `K` is by continuous automorphisms, this
identification is `Lambda`-equivariant for the dual action on `A`.  Taking
crossed products therefore gives `(ACGF1)` and preserves the canonical trace.

If `A rtimes Lambda` were hyperlinear, `L(A rtimes Lambda)` would embed
trace-preservingly into `R^omega`.  Restricting that embedding to the assumed
von Neumann subalgebra `N` would make `N` Connes embeddable, contradiction.
The optional finite-presentation conclusion is Higman's theorem followed by
the elementary fact that every subgroup of a hyperlinear group is
hyperlinear.

