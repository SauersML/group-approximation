---
rg: 2
id: berend-quotient-return-map-defect-proof
kind: route
title: Apply a finite-set logarithm path to the surviving K-class and force loss of invertibility
target: berend-quotient-return-maps-have-maximal-defect
requires:
  - berend-integral-k-theory-and-invisible-class
artifacts:
  - research/artifacts/berend-k-theory-quotient-obstruction-2026-09-05.md
---

The finite-orbit image of the witness unitary has trivial K-class.
Homomorphic return preserves this vanishing, whereas the original
unitary has nonzero K-class. Two unitaries at distance less than two
have the same K-class, giving exact distance two for a unital
homomorphic return map.

For a unital completely positive return map choose a selfadjoint
`h in M_k(C(F))`, `||h||<=pi`, with `exp(i h)=q_F^(k)(v)`. Its image
path `x(t)=sigma^(k)(exp(i t h))` starts at `1` and ends within distance
less than one of `v`, so its endpoint is invertible with the same
nonzero K-class as `v`. The path must cross a noninvertible contraction
`x(t_0)`. If both `||1-x(t_0)^*x(t_0)||` and
`||1-x(t_0)x(t_0)^*||` were less than one, it would have left and right
inverses. Thus one of these norms equals one. The corresponding input
`w=exp(i t_0 h)` is the required unitary. The artifact spells out why
the quotient-dependent witness does not give a contradiction to finite
decomposition rank.
