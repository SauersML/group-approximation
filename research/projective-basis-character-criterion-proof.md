---
rg: 2
id: projective-basis-character-criterion-proof
kind: route
title: Quotient the scalar kernel and read orthogonality from the GNS character
target: projective-basis-character-criterion
requires: []
---

Equality in Cauchy--Schwarz for the unit vectors `pi_chi(g)1` and `1` gives

```text
|chi(g)|=1  iff  pi_chi(g) is scalar.
```

Thus the scalar kernel `N_chi` is normal. Choose a section
`s:G/N_chi->G`. Images belonging to distinct cosets are orthogonal exactly
when `chi` vanishes off `N_chi`; images in one coset differ by a scalar. Their
linear span is GNS-dense, proving the basis criterion. Section multiplication
produces the scalar cocycle `omega` and identifies the GNS algebra with the
twisted group factor.

If a rephasing makes `omega` `mu_m`-valued, then `[omega]^m=1`. Conversely,
if `omega^m=delta b`, choose a scalar cochain `a` with `a^m=b^(-1)`. Then
`(delta a times omega)^m=1`, so the rebased multiplier takes values in
`mu_m`.
