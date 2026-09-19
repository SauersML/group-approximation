---
rg: 2
id: support-only-toeplitz-return-cannot-see-heat-decay
kind: claim
title: A support-only Toeplitz return cannot see heat-filter norm decay
distinct_from:
  fanizza-heat-return-is-one-cyclic-amplitude-product: that supplies a positive scalar endpoint using the amplitude square; this rules out replacing it by carrier rank alone.
  rectangular-escape: that enlarges label space while shrinking multiplicity; this obstruction already occurs on one fixed carrier with no rectangular label change.
  universal-block-return-violates-the-regular-firewall: that rules out tracially functorial unequal-rank products; this shows why equal-rank support transport has no access to the heat estimate.
---

There is no dimension-independent function `f(alpha)->0` such that every
finite-dimensional contraction `B` satisfies

```text
rank(supp(B))/d <= f(||B||).                           (SHT1)
```

Indeed `B=alpha I_d` has arbitrarily small norm and full support.  The same
obstruction applies to the Fanizza filters: a polynomial `p_t(H_m)` can be
nonzero on every eigenvalue in a finite model, so
`D_R p_t(H_m)` may retain the full `D_R`-support even while its operator norm
is `O(1/t)`.

Therefore a Toeplitz/Leavitt mechanism which transports only source and
target support projections, integer multiplicities, or Murray--von Neumann
carrier classes cannot consume `(FHR1)` or `(FHR2)`.  An equal-support return
sees no loss; a proper-support return would need a separately decoded
spectral cutoff and is again the unresolved finite-matrix selection problem.

The heat route must preserve amplitude in the returned product.  The minimal
known form is `(HAP3)` from
`fanizza-heat-return-is-one-cyclic-amplitude-product`, with target
`B_t^*B_t`, or an authenticated matrix-dependent spectral projection whose
rank is bounded from `(HAP2)`.  Plain Toeplitz shift multiplicity supplies
neither.

This also explains why the properly infinite HALT extension is easy but not
decisive.  Infinite multiplicity can identify all support carriers, and the
perfect quotient has amplitude one on the signal.  The missing distinction
is forcing finite matrices to remember the small NONHALT amplitude rather
than replacing it by a full-support equivalent carrier.
