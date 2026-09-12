---
rg: 2
id: mci-exact-endpoint-fd-radical-proof
kind: route
title: Evaluate the cyclic-invariance modulus at zero defect
target: mci-exact-endpoint-is-fd-radical
requires: []
---

An exact finite-dimensional representation has presentation defect zero, so
the cyclic-invariance estimate applies for every positive `delta`. Letting
`delta` tend to zero makes the sum of nonnegative commutator energies vanish,
hence every `[s,f(w)]` is killed.

If one of these finite-support group-algebra elements is nonzero and `G` is
residually finite, intersect finitely many finite-index kernels to obtain a
finite quotient injective on its support. Distinct support elements remain
distinct basis vectors in the finite group algebra, and the quotient regular
representation detects the image. This contradicts finite-dimensional
radical membership.

Finally, in fixed dimension the compact sets of unitary tuples with defect at
most `delta` decrease to the exact representation variety. Continuity of the
energy gives a modulus in that dimension. Nothing in this compactness argument
is uniform as the dimension tends to infinity.
