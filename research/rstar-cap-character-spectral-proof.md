---
rg: 2
id: rstar-cap-character-spectral-proof
kind: route
title: Read a maximal-cap one-fibre on the joint spectrum
target: rstar-cap-support-is-one-character-row
requires:
  - rstar-fano-caps-have-seven-maximal-parity-covers
---

On the joint atom indexed by `x`, the spectral value of `(FCH1)` is

```text
(-1)^(a_2 x_2+a_3 x_3+a_4 x_4).                        (FCH6)
```

Therefore `Y_a=-I` exactly when every positive joint atom belongs to the
one-fibre `C_a`.  The established maximal-cap theorem says that a support is
a Fano cap exactly when it is contained in one such fibre.  This proves all
three local conditions in `(FCH2)` equivalent.

Apply the equivalence independently at the `m` nonlinear contexts.  Choosing
their nonzero functionals gives `(FCH3)` and one of `7^m` profiles.  In the
usual involution presentation, `Y_(a_c)=-I` is precisely the parity equation
`(FCH5)`; perfectness already supplies `(FCH4)`.  Conversely, those two rows
put every local atom in `C_(a_c)`, hence in `R_*`, and force `(FCH1)` to be
`-I`.  Thus satisfying a character profile is the same as factoring through
its affine LCS quotient.
