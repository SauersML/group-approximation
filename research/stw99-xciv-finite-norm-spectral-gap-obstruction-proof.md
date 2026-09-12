---
rg: 2
id: stw99-xciv-finite-norm-spectral-gap-obstruction-proof
kind: route
title: Preserve spectral diameter under every unital Z embedding
target: stw99-xciv-finite-norm-spectral-gap-is-negative-certificate
requires: []
---

Choose a non-scalar selfadjoint element of `Z` and affinely normalize it to
an element `h` of spectral diameter `1`.  Every unital homomorphism
`phi:Z->B` is nonzero, hence injective because `Z` is simple.  It therefore
preserves the spectrum of `h`.  For a selfadjoint element, distance to the
scalar multiples of the unit is half its spectral diameter, so

```text
dist(phi(h),C 1_B)=1/2.
```

Apply the assumed spectral-gap inequality to `y=phi(h)`.  This gives

```text
1/2 <= kappa max_{a in F} ||[phi(h),a]||,
```

which is the claimed lower bound.  It contradicts the local norm-central
criterion `stw99-xciv-separable-zstability-iff-local-norm-central-z` with
`G={h}` and any `epsilon<1/(2kappa)`.  Hence `B` cannot be separably
`Z`-stable.
