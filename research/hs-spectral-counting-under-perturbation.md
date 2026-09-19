---
rg: 2
id: hs-spectral-counting-under-perturbation
kind: claim
title: Hilbert--Schmidt perturbation controls spectral counting across a fixed gap
---

Let `A,C` be self-adjoint operators on an `N`-dimensional Hilbert space, use
the normalized Hilbert--Schmidt norm and normalized trace, and fix `a<b`.
Then

```text
tr(1_((minus infinity,a])(A))
 <= tr(1_((minus infinity,b])(C)) + ||A-C||_2^2/(b-a)^2,        (HSC1)
```

and the symmetric inequality holds after exchanging `A,C`.

Thus normalized spectral rank is stable under normalized-HS perturbation as
long as the two counting thresholds leave a fixed gap. No operator-norm
control and no dimension-dependent constant is required.

