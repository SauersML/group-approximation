---
rg: 2
id: junge-code-riesz-literature-audit-proof
kind: route
title: Compare the cnd Riesz and martingale BMO theorems with the code inverse
target: junge-riesz-bmo-does-not-close-code-newton
requires:
  - code-riesz-inverse-is-averaged-first-split
  - code-laplacian-has-uniform-cp-green-approximants
---

Primary-source audit:

* Junge--Mei--Parcet,
  [Noncommutative Riesz transforms---dimension free bounds and Fourier
  multipliers](https://arxiv.org/abs/1407.2475), Theorems A1--A2 and the
  authors' explicit endpoint warning in the introduction.
* Junge--Musat,
  [A noncommutative version of the John--Nirenberg
  theorem](https://arxiv.org/abs/math/0410121), Theorems 1.1--1.2.

For `(JRB1)`, take the real Hilbert space with coordinate basis, let `z` act
by coordinate signs, and set the cocycle coordinate to `0` or `1` according
to `z_i`; the cocycle identity is the bit identity
`(u+v)=u+(-1)^u v`, and its squared norm is Hamming weight.  This verifies
the JMP hypothesis.

Reading the displayed symbols in Theorem A1 gives the extra
`psi^(-1/2)` factor in the code inverse.  The theorem range and the explicit
failure to obtain the BMO endpoint are literal statements in that paper.
Junge--Musat's hypotheses are one increasing filtration with conditional
expectations; its large-deviation conclusion is one projection for one BMO
element and one-sided operator control.  Comparing these statements with
the first-split identity proves every boundary recorded in the claim.
