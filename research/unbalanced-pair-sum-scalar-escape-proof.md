---
rg: 2
id: unbalanced-pair-sum-scalar-escape-proof
kind: route
title: Evaluate the all-ones syndrome character and count parity-layer weight
target: unbalanced-pair-sum-overlay-has-scalar-syndrome-escape
requires: []
---

For `Q_i=(-1)^(z_i)I`, the parity sign of row `h_a` is
`(-1)^((Hz)_a)=-1`, whereas the sign of `h_a+h_b` is
`(-1)^((Hz)_a+(Hz)_b)=1`.  All commutator and equality relations are exact.
There are `M` bad original faces among `M+M(M-1)/2` total faces, proving the
vanishing normalized defect.

For every exact code character `c`, the difference `z+c` has all `M`
syndrome bits nonzero.  A coordinate belongs to at most `D` rows, so its
support must contain at least `M/D` coordinates.  Scalar signs differing on
one coordinate have squared normalized-HS distance four.  This proves the
claimed constant correction lower bound and the balancing prescription.
