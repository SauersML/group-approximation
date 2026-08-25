---
rg: 2
id: jnvwy-canonical-unsafe-support-proof
kind: route
title: Follow the nonlinear axis-line sampler graph through the honest compression chain
target: jnvwy-canonical-halt-strategy-is-affine-unsafe
requires:
  - jnvwy-low-degree-pcp-reflects-affine-unsafety
---

Use the effective coherent completeness choices and the explicit calculation
given in the target claim.  For the answer-reduction axis-line sampler,
`chi(0)=1`, `chi(q/m)=2`, and the two corresponding deletion maps disagree on
`e_2`.  This gives three uniform seeds whose graph points have a rejected odd
xor.  The same sampler component remains a direct summand under detyping,
anchoring, and repetition by fixing all new control and repetition coordinates.

At the first genuine recursion step the source answer is the fixed zero
answer, so honest EPR-Z introspection puts every one of those three graph
points in positive Intro--Sample support.  The required reflection claim
carries that certificate through the characteristic-two answer reduction;
oracularization, anchoring, and repetition preserve it by fixing their other
coordinates.  The Intro--Intro game test embeds the previous bad source atom
at every earlier recursion step, so downward induction gives the asserted bad
support at the output index.
