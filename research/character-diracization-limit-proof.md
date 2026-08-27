---
rg: 2
id: character-diracization-limit-proof
kind: route
title: GNS computation of the two-norm defect plus a scalar power
target: character-diracization-limit
requires: []
---

Direct proof, given in the claim: expand `||u_g - tau(g)1||_2^2` in the
tracial GNS algebra to get `1 - |tau(g)|^2`, read off that `|tau(g)| = 1`
means `u_g` is scalar, note that the preimage of the scalars is normal
because conjugation fixes scalars, and take `k`-th powers of a number in
`[0,1]`.  Positive-definiteness of `|tau|^{2k}` is the Schur product theorem
in the form "pointwise product of characters is the character of the tensor
product", with `conj(tau)` the character of the conjugate representation.

The IRS corollary is independence of `k` iid samples,
`Pr[g in H_1 ∩ ... ∩ H_k] = Pr[g in H]^k`, and conjugation-invariance of `mu`
making `{g : Pr[g in H] = 1}` normal.  No external input.
