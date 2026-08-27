---
rg: 2
id: central-hnn-inversion-symmetrized-trace-is-mf
kind: claim
title: A central-HNN trace whose base quotient representation asymptotically lifts becomes MF after stable-letter inversion symmetrization
artifacts:
  - research/artifacts/shulman-central-hnn-inversion-lifting-audit-2026-08-22.md
distinct_from:
  shulman-symmetric-double-has-no-stable-trace-upgrade: that rules out an incorrectly attributed theorem for all traces on a symmetric amalgam; this is a direct conditional consequence of Shulman's genuine homotopy-lifting theorem for one quotient representation.
  sl3-hnn-sits-in-shulman-symmetric-double: that imports operator-norm MF of an ambient full C-star algebra without selecting a trace; this selects the inversion-symmetrized trace but assumes an asymptotic lift of the same base quotient representation.
  hnn-over-codense-kazhdan-subgroup-not-hyperlinear: that uses global Hilbert--Schmidt stability of the base group to correct every base microstate; this only identifies the representation-specific operator-norm lifting hypothesis needed by the homotopy argument.
---

Let `A` be a separable unital C-star algebra, let `C <= A` be a unital
C-star subalgebra, and let

```text
D = < A,t | t unitary and [t,C]=0 >
```

be the full central HNN C-star algebra.  Let `iota` be the automorphism of
`D` fixing `A` and sending `t` to `t*`.  Suppose

```text
f:D -> Q_2 = prod M_(d_n) / direct-sum_(2,omega) M_(d_n)
```

is a homomorphism and the restriction `f|A` lifts to a discrete asymptotic
homomorphism into `prod M_(d_n)`.  If `tau=tr o f`, then

```text
tau_sym = (tau + tau o iota)/2                         (CHI1)
```

is an MF trace on `D`.

In particular, if `tau o iota=tau` (as for the canonical trace of a group
central HNN extension), then `tau` itself is MF under the same
representation-specific base-lifting hypothesis.

This is not a stability theorem.  Hyperlinearity of `tau|A`, or even the
existence of some MF model for that restricted trace, does not say that the
particular homomorphism `f|A` lifts.  Thus `(CHI1)` exposes rather than
removes the missing correction/lifting step in the arithmetic HNN lane.
