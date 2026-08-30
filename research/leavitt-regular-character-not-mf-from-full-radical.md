---
rg: 2
id: leavitt-regular-character-not-mf-from-full-radical
kind: route
title: A regular-character model would faithfully embed the full-radical group
target: leavitt-regular-character-is-not-mf
requires:
  - binary-leavitt-all-ranks-full-mf-radical
---

Put `H=EL_n(L_(F_2)(1,2))`, `n>=3`, and suppose maps
`V_k:H->U(d_k)` have pointwise operator-norm multiplicative defect tending
to zero and normalized traces tending to the regular character.  They induce
a homomorphism

```text
rho:H -> U(prod_k M_(d_k) / direct-sum_k M_(d_k)).
```

For every `g!=1`,

```text
||V_k(g)-1||_(2,tr)^2 = 2-2 Re tr_(d_k)(V_k(g)) -> 2.
```

Since normalized Hilbert--Schmidt norm is bounded by operator norm,
`liminf_k ||V_k(g)-1||_op >= sqrt(2)`.  Thus `rho(g)!=1` and `rho` is
injective.  Hence `H` is operator-MF.

But `binary-leavitt-all-ranks-full-mf-radical` gives
`Rad_MF(H)=H`: every homomorphism from `H` to an operator-MF group is
trivial.  Applying this to the injective map into the matrix-corona unitary
group is a contradiction.  Therefore the regular character admits no such
models.

This proof uses the established Kazhdan-derived full-radical theorem.  It
establishes the unrestricted proposition only; it does not establish
`leavitt-regular-character-not-mf-without-property-t`.
