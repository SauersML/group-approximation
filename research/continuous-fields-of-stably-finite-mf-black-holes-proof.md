---
rg: 2
id: continuous-fields-of-stably-finite-mf-black-holes-proof
kind: route
title: Tensor the reduced Hilbert-hotel black hole with a faithful commutative trace
target: continuous-fields-of-stably-finite-mf-black-holes
requires:
  - reduced-cstar-mf-black-hole-absorption
---

The map `a |-> 1 tensor a` embeds `C*_r(H)` unitally into `A_X`, so upward
black-hole absorption kills every MF-target homomorphism from `A_X`.

Choose a probability measure of full support on `X`.  Integrating the tensor
product of this measure with the canonical faithful trace on `C*_r(H)` gives
a faithful trace on `A_X`: a nonzero positive continuous section has positive
trace on a neighborhood of a point where it is nonzero.  The same argument
on every matrix amplification proves stable finiteness.

Separable unital quasidiagonal algebras are MF.  Hence a nonzero MF or
quasidiagonal quotient would give a forbidden nonzero target homomorphism.
