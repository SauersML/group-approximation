---
rg: 2
id: kt-c-normalization-relative-cocycle-proof
kind: route
title: Divide the two Gamma implementations and compute the kernel gauge action
target: kt-c-normalization-seam-is-a-relative-commutant-cocycle
requires:
  - kt-one-compressor-and-sl3-normalizer-lifts-paste
  - kt-c-normalization-is-the-first-finite-normalizer-seam
---

Both `v_gamma` and `rho_gamma` restrict by conjugation to
`alpha_(alpha_C(gamma))` on `R`, so their quotient lies in `K`.  Since `v`
and `rho` are representations of `Gamma`, writing
`v_gamma=k_gamma rho_gamma` gives

```text
v_gamma v_delta
 =k_gamma rho_gamma k_delta rho_delta
 =k_gamma beta_gamma(k_delta) rho_(gamma delta),
```

which is `(KCC2)`.  Replacing `u_C` by `z u_C` replaces `v_gamma` by
`z v_gamma z^*`; division on the right by `rho_gamma` gives `(KCC3)`.
Finally `k'_gamma=1` is equivalent to `(KCC4)`, and rearranging `(KCC3)`
gives `(KCC5)`.  Generator rows propagate to all of `Gamma` because both
sides of `(KCC4)` are homomorphisms.
