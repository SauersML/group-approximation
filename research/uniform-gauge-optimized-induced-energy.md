---
rg: 2
id: uniform-gauge-optimized-induced-energy
kind: claim
title: Uniform induced edge energy after optimizing the exact BS core
distinct_from:
  gauge-optimized-induced-energy-target: that defines the optimized functional, proves its sufficiency, and checks the scalar counterfamily; this is the still-open assertion that the functional is uniformly bounded by presentation energy.
  induced-rounding-needs-rms-section-fillings: that freezes the input core and is false uniformly; this permits every nearby exact core before forming the induced section.
  gauge-optimized-target-has-uniform-congruence-tangent-gap: that proves the linearization of this statement on the locally exact congruence tangent slice; this asks for its global nonlinear normalized-HS form.
---

With `G_N` and `E_end` defined in
`gauge-optimized-induced-energy-target`, prove that one constant `C` works
for every dyadic level `N=4^K-1`, every dimension, every exact level-`N`
BS core `b`, and every involution `X`:

```text
G_N(X,b) <= C E_end(X,b).                              (UGO1)
```

Flexible padding may be included in the competitors in `G_N`, with its
relative rank charged as an additional nonnegative term.

The congruence tangent quotient has a uniform gap, so `(UGO1)` has no
moving-level infinitesimal obstruction.  Its content is nonlinear
integration in normalized HS after quotienting the complete exact-core
variety.

## Attempts

- Frozen-core induction is false: the `r`-exponent character gives constant
  section energy from `O(K^(-2))` relator energy.  Optimizing the exact core
  absorbs this family at the correct scale.
- The stronger endpoint-conjugation counterpacket which refutes aggregate
  Iwahori inverse energy is also absorbed exactly. For
  `X_z=zXz^(-1)`, choose the competitor core
  `(zRz^(-1),T)`. The hybrid tuple is a conjugate exact endpoint, so its
  section energy is zero; the core-motion cost is
  `||z-psi(z)||_2^2`. On the first-mode left regular family this is at most
  `16 E_end` for sufficiently small amplitude. See
  `optimized-core-absorbs-endpoint-conjugations`.
- Ordinary HS Newton integration is unavailable because operator-large
  rank-one directions have no dimension-free quadratic Taylor remainder.
- Spectral thresholding isolates the operator-large residual on rank
  `O(E/theta^2)`, but its BS-invariant hull can have full packet rank.
  Therefore the active carrier must be paired and reconnected through the
  two cubic polar ranges without first taking an invariant hull.  This is
  the reverse active-dilation problem in
  `bs14-residual-polar-data-build-active-dilation`.
