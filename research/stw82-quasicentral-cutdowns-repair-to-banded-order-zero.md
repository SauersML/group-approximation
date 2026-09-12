---
rg: 2
id: stw82-quasicentral-cutdowns-repair-to-banded-order-zero
kind: claim
title: Quasicentral cutdowns of one finite-dimensional order-zero colour repair inside their spectral bands
distinct_from:
  stw82-spectral-interval-band-depth-reuses-colours: that colours maps already having common-cut spectral supports; this constructs such band-local order-zero maps from a single outgoing colour by cutting and perturbing.
  stw82-raw-two-cut-reuse-iff-quasidiagonal: that asks to perturb complementary cut supports themselves to orthogonal supports and is equivalent to quasidiagonality; this permits overlapping bands and perturbs the maps inside hereditary band algebras.
---

Fix a finite-dimensional C*-algebra `F`, a positive integer `m`, and
`epsilon>0`.  There is `delta>0` with the following property.

Let `B` be a C*-algebra, let `phi:F->B` be cpc order zero, and let
`c_1,...,c_m` be positive contractions in `M(B)` satisfying

```text
sum_i c_i=1_(M(B)),                                    (S1)
```

and, for every `x` in the unit ball of `F`,

```text
max_i max(
  norm([c_i,phi(x)]),
  norm([c_i^(1/2),phi(x)])
) < delta.                                             (S2)
```

Put

```text
B_i=closure(c_i^(1/2) B c_i^(1/2)).                    (S3)
```

Then there are cpc order-zero maps `psi_i:F->B_i` such that

```text
norm(phi-sum_i psi_i)<epsilon.                         (S4)
```

Moreover, if the indices are partitioned into classes so that
`c_i c_j=0` for distinct indices in one class, then the direct sum of the
`psi_i` in each class is cpc order zero.

In particular, take `c_i=g_i(h)` for a positive contraction `h in M(B)`
and a finite positive partition of unity `(g_i)` on `[0,1]`.  As `h`
becomes quasicentral for `phi(F)`, (S2) holds.  Thus one outgoing
finite-dimensional order-zero colour admits arbitrarily accurate
subdivision into exact order-zero maps which remain inside the prescribed
hereditary spectral bands.  No projectional approximate unit, nuclearity,
stability, or extension fullness is required.
